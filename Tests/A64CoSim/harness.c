// Native arm64 co-simulation harness (doc/design/targets.md, ISA models: co-simulation; doc/design/trust.md, Evidence beyond proofs).
//
//   a64cosim-run CASES EXPECT
//
// CASES is written by `lake exe a64cosim gen`: records of
//   u64 n; u32 code[64]; u64 x[31]; u64 sp; u64 nzcv; u8 window[512];
//   u64 sys; u64 inlen; u8 in[16]                                              (1072 bytes)
// EXPECT holds the Lean model's outcome for each case:
//   u64 status (0: reached the end, 1: fault, 2: exit); u64 x[31]; u64 sp; u64 nzcv;
//   u8 window[512]; u64 code; u64 outlen; u8 out[32]                          (832 bytes)
// For each case the harness writes the code into a fixed executable page (CODE, see stub.S for
// the layout: entry stub, the n instructions at TEST, exit stub), the window into a fixed
// read-write page (DATA), runs it on this CPU, and compares the outcome with the model's. A fault
// (SIGSEGV, SIGBUS: an unmapped or non-writable page, the stack-alignment check, a misaligned pc)
// is caught on an alternate stack; then only the status is compared. A case with `sys` set makes
// system calls: it runs in a child process whose standard input is a pipe holding `in` and whose
// standard output is a pipe, and the outcome adds the exit code, if it called `exit`, and the
// bytes it wrote.
// Exit status 0 iff every case agrees; the first disagreements are printed field by field.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#define CODE 0x10000000UL
#define TEST (CODE + 0x400)
#define DATA 0x20000000UL
#define WIN 512
#define MAXN 64

struct rec { uint64_t n; uint32_t code[MAXN]; uint64_t x[31], sp, nzcv; uint8_t win[WIN];
             uint64_t sys, inlen; uint8_t in[16]; };
struct out { uint64_t status; uint64_t x[31], sp, nzcv; uint8_t win[WIN];
             uint64_t code, outlen; uint8_t outb[32]; };
struct ctx { uint64_t x[31], sp, nzcv, hsp, htpidr, save[12]; };

extern char entry_tmpl[], entry_tmpl_end[], exit_tmpl[], exit_tmpl_lit[], exit_tmpl_end[];

static sigjmp_buf jb;
static volatile uint64_t host_tpidr;
static struct ctx c;
static struct out *shared;
static uint8_t *code_page;

// Runs the case loaded in the code page and the window, and writes its outcome to `o`: the
// registers, sp, NZCV and window, or status 1 after a fault.
static void run_case(struct out *o, uint8_t *data) {
  if (sigsetjmp(jb, 1) == 0) {
    ((void (*)(struct ctx *))code_page)(&c);
    memcpy(o->x, c.x, sizeof o->x);
    o->sp = c.sp;
    o->nzcv = c.nzcv;
    memcpy(o->win, data, WIN);
  } else {
    o->status = 1;
  }
}

static void on_fault(int sig) {
  (void)sig;
  __asm__ volatile("msr tpidr_el0, %0" ::"r"(host_tpidr));
  siglongjmp(jb, 1);
}

static int read_all(const char *path, void **buf, size_t *len) {
  FILE *f = fopen(path, "rb");
  if (!f) return -1;
  fseek(f, 0, SEEK_END);
  *len = (size_t)ftell(f);
  fseek(f, 0, SEEK_SET);
  *buf = malloc(*len + 1);
  if (fread(*buf, 1, *len, f) != *len) return -1;
  fclose(f);
  return 0;
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: %s CASES EXPECT\n", argv[0]); return 2; }
  void *cb, *eb;
  size_t cl, el;
  if (read_all(argv[1], &cb, &cl) || read_all(argv[2], &eb, &el)) { perror("read"); return 2; }
  size_t ncase = cl / sizeof(struct rec);
  if (cl % sizeof(struct rec) || el != ncase * sizeof(struct out)) {
    fprintf(stderr, "a64cosim-run: bad file sizes %zu %zu\n", cl, el); return 2;
  }
  uint8_t *code = mmap((void *)CODE, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
  uint8_t *data = mmap((void *)DATA, 4096, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
  if (code != (void *)CODE || data != (void *)DATA) { perror("mmap"); return 2; }
  code_page = code;
  shared = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (shared == MAP_FAILED) { perror("mmap"); return 2; }
  stack_t ss = { .ss_sp = malloc(1 << 16), .ss_size = 1 << 16, .ss_flags = 0 };
  sigaltstack(&ss, NULL);
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = on_fault;
  sa.sa_flags = SA_ONSTACK | SA_NODEFER;
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
  sigaction(SIGILL, &sa, NULL);
  __asm__ volatile("mrs %0, tpidr_el0" : "=r"(host_tpidr));

  size_t elen = (size_t)(entry_tmpl_end - entry_tmpl), xlen = (size_t)(exit_tmpl_end - exit_tmpl);
  if (elen > TEST - CODE) { fprintf(stderr, "entry stub too long\n"); return 2; }
  int bad = 0, faults = 0;
  for (size_t k = 0; k < ncase; k++) {
    struct rec *r = (struct rec *)cb + k;
    struct out *e = (struct out *)eb + k, o;
    memset(&o, 0, sizeof o);
    mprotect(code, 4096, PROT_READ | PROT_WRITE);
    memset(code, 0, 4096);
    memcpy(code, entry_tmpl, elen);
    uint64_t bpc = CODE + elen - 4;
    *(uint32_t *)(code + elen - 4) = 0x14000000u | (uint32_t)(((TEST - bpc) / 4) & 0x3ffffff);
    memcpy((void *)TEST, r->code, 4 * r->n);
    uint8_t *exit = (uint8_t *)TEST + 4 * r->n;
    memcpy(exit, exit_tmpl, xlen);
    *(uint64_t *)(exit + (exit_tmpl_lit - exit_tmpl)) = (uint64_t)&c;
    mprotect(code, 4096, PROT_READ | PROT_EXEC);
    __builtin___clear_cache((char *)code, (char *)code + 4096);
    memset(data, 0, 4096);
    memcpy(data, r->win, WIN);
    memcpy(c.x, r->x, sizeof c.x);
    c.sp = r->sp;
    c.nzcv = r->nzcv;
    if (!r->sys) {
      run_case(&o, data);
    } else {
      // in a child, with pipes for standard input and output; `shared` receives the outcome
      // unless the case calls `exit`
      int ip[2], op[2];
      if (pipe(ip) || pipe(op)) { perror("pipe"); return 2; }
      if (write(ip[1], r->in, r->inlen) != (ssize_t)r->inlen) { perror("write"); return 2; }
      close(ip[1]);
      memset(shared, 0, sizeof *shared + 8);
      pid_t pid = fork();
      if (pid == 0) {
        dup2(ip[0], 0);
        dup2(op[1], 1);
        close(ip[0]); close(op[0]); close(op[1]);
        run_case(shared, data);
        *(uint64_t *)(shared + 1) = 1;  // finished without `exit`
        _exit(0);
      }
      close(ip[0]);
      close(op[1]);
      int st = 0;
      waitpid(pid, &st, 0);
      if (*(uint64_t *)(shared + 1) == 1) {
        memcpy(&o, shared, sizeof o);
      } else if (WIFEXITED(st)) {
        o.status = 2;
        o.code = (uint64_t)WEXITSTATUS(st);
      } else {
        o.status = 3;  // killed by a signal: never what the model says
      }
      ssize_t got = read(op[0], o.outb, sizeof o.outb);
      o.outlen = got > 0 ? (uint64_t)got : 0;
      close(op[0]);
    }
    if (o.status == 1) faults++;
    if (memcmp(&o, e, sizeof o) != 0) {
      if (++bad <= 5) {
        printf("a64cosim: case %zu differs (hardware vs model):\n", k);
        if (o.status != e->status)
          printf("  status: hardware %s, model %s\n", o.status ? "fault" : "ok",
                 e->status ? "fault" : "ok");
        else {
          for (int i = 0; i < 31; i++)
            if (o.x[i] != e->x[i])
              printf("  x%d: %016lx vs %016lx\n", i, o.x[i], e->x[i]);
          if (o.sp != e->sp) printf("  sp: %016lx vs %016lx\n", o.sp, e->sp);
          if (o.nzcv != e->nzcv) printf("  nzcv: %08lx vs %08lx\n", o.nzcv, e->nzcv);
          if (o.code != e->code) printf("  exit code: %lu vs %lu\n", o.code, e->code);
          if (o.outlen != e->outlen || memcmp(o.outb, e->outb, sizeof o.outb))
            printf("  output: %lu vs %lu bytes, or different bytes\n", o.outlen, e->outlen);
          for (int i = 0; i < WIN; i++)
            if (o.win[i] != e->win[i])
              printf("  mem[DATA+%d]: %02x vs %02x\n", i, o.win[i], e->win[i]);
        }
        printf("  code:");
        for (uint64_t i = 0; i < r->n; i++) printf(" %08x", r->code[i]);
        printf("\n");
      }
    }
  }
  if (bad) { printf("a64cosim: %d of %zu cases differ\n", bad, ncase); return 1; }
  printf("a64cosim: OK (%zu cases agree with this CPU, %d of them faulting)\n", ncase, faults);
  return 0;
}
