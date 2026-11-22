// The reference for Tests/A64Obj.lean `echo` (scripts/a64-elf-check.sh): the same program,
// instruction for instruction and in the same order, assembled by llvm-mc and linked by ld.lld
// (and by gcc/GNU ld) at the section addresses Millipede's linker chose. The .text bytes of
// the two links must be identical, which checks every fixup Millipede applied.
        .text
        .globl _start
_start:
        // write(1, hello, 6)
        mov x0, #1
        adrp x1, hello
        add x1, x1, :lo12:hello
        mov x2, #6
        mov x8, #64
        svc #0
        // n = read(0, buf, 64); write(1, buf, n)
        mov x0, #0
        adrp x1, buf
        add x1, x1, :lo12:buf
        mov x2, #64
        mov x8, #63
        svc #0
        orr x2, xzr, x0
        mov x0, #1
        adrp x1, buf
        add x1, x1, :lo12:buf
        mov x8, #64
        svc #0
        mov x9, #3
loop:   sub x9, x9, #1
        cbnz x9, loop
        b skip
        ret
skip:   adr x5, loop
        bl far
        adrp x3, val
        add x3, x3, :lo12:val
        ldr x0, [x3]
        mov x8, #93
        svc #0
pad:    .rept 320000
        orr x10, xzr, xzr
        .endr
far:    mov x0, #1
        adrp x1, farmsg
        add x1, x1, :lo12:farmsg
        mov x2, #4
        mov x8, #64
        svc #0
        ret

        .section .rodata
val:    .quad 42
hello:  .ascii "hello\n"
farmsg: .ascii "far\n"

        .bss
buf:    .zero 64
