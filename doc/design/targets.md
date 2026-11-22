# Targets

Millipede compiles for two targets, x64 Linux and arm64 Linux. A target is a Lean value of type
`Target` that bundles an instruction-set model, a model of the Linux system calls on that
instruction set, an executable format with its loader model, a cost model and a frame model. The
compiler and its proofs are written once for every target, so this document describes only what
each target supplies.

Both targets produce static ELF executables that call the kernel directly with three system
calls, `read`, `write` and `exit`. They use no C library and no dynamic linking.

## ISA models

An instruction-set model, or ISA model, gives an instruction type, a register file, an encoder,
a decoder, and the effect of executing one instruction. One machine step fetches the bytes at the
program counter from executable memory, decodes them and executes the instruction. A step that
cannot decode its bytes, or that faults, leaves the machine stuck.

Each model covers only the instructions that the compiler emits. Any other byte sequence fails to
decode. The correctness theorem shows that compiled code never gets stuck, so it never reaches an
instruction outside the model, and an instruction left out of the model cannot make the theorem
false. Only a mistake in what is modelled can.

The x64 model has the 16 general registers, the instruction pointer `rip`, and the flags CF, ZF,
SF and OF. Its instructions are 64-bit moves, loads and stores, byte loads and stores, `lea`,
`add`, `sub`, `and`, `or`, `xor`, `cmp`, `imul`, `div`, shifts by `cl`, `setcc`, `movzx`, the
conditional and unconditional jumps, `call`, `ret`, `push`, `pop` and `syscall`. A memory operand
is a base, optionally plus an index (scale 1), with a 32-bit displacement, or relative to `rip`;
a data access is `lea r11, [rip + mp_mem]` then `[r11 + a + off]`. Stores of immediates
(`mov qword [m], imm32`, `mov byte [m], imm8`) and `op r, imm32` take sign-extended 32-bit values. `div` faults when
the divisor is zero, and an access to a non-canonical address faults. Where Intel leaves a flag
undefined the model makes a fixed choice, and compiled code never reads such a flag.

The arm64 model has the registers `x0` to `x30`, the stack pointer, the program counter and the
flags N, Z, C and V. Every instruction is one 32-bit word. The subset has `movz`, `movn` and
`movk` for constants, addition and subtraction, the logical operations, multiply-add, division,
shifts and bit-field moves, conditional selects, loads and stores of every width, `adr` and
`adrp`, the branches `b`, `bl`, `b.cond` and `cbz`, `ret` and `svc`. Division by zero gives zero.
A load or store based on `sp` faults when `sp` is not a multiple of 16, as Linux enables that
check for user code. Every function's entry sets `x29` to the data region's address
(`adrp`, `add`), nothing else writes it, and a load or store of the data region is `[x29, a]` or
`add x16, a, #off; [x29, x16]`.

Each model proves the same laws. Decoding an encoded instruction gives the instruction back with
its length. An instruction other than the system call changes only the registers and memory
bytes it names, and leaves the world unchanged. Instruction fetch reads only executable memory,
and a store needs writable memory. Some lemmas about the bits of encodings are proved with the
tactic `bv_decide`, which the project allows nowhere else.

## ABI models

The system-call model of a target says how a program asks the kernel for a system call. It reads
the call number and the arguments from registers, reads the bytes of any buffer the call takes
from memory, passes the call to the oracle, writes the bytes the oracle returns into the output
buffer, and writes the result word back. A call with an unknown number, or a buffer the program
cannot read, leaves the machine stuck. After `exit` the machine stays where it is.

The two targets differ only in where these things are.

| | x64 Linux | arm64 Linux |
|---|---|---|
| instruction | `syscall` | `svc #0` |
| call number | `rax`: `read` 0, `write` 1, `exit` 60 | `x8`: `read` 63, `write` 64, `exit` 93 |
| arguments | `rdi`, `rsi`, `rdx` | `x0`, `x1`, `x2` |
| result | `rax` | `x0` |
| registers changed | `rax`, and `rcx` and `r11` by the instruction | `x0` only |

At process entry every register is zero except the stack pointer. The stack lies below a fixed
address, `0x7ffffffff000` on x64 and `0x7fffff0000` on arm64. Linux places the stack at a random
address, but compiled code never observes an address, so the model's fixed choice cannot be
seen.

## The internal calling convention

Calls between Millipede functions use a convention of Millipede's own, which is the same in
shape on both targets. A function with a frame of `F` slots reserves its frame on entry, and slot
`x` is the word at `sp + 8x`. On x64 the return address lies just above the frame. On arm64 the
frame also holds the saved link register `x30`, and its size is rounded up to a multiple of 16
bytes, or of 4 KiB from 510 slots on, so that one instruction can reserve it.

To call a function with a frame of `G` slots, the caller writes the arguments and zeros directly
into the words that will be the callee's frame, then calls it. It writes only the words of the
callee's locations that are live at the callee's entry, since the callee writes the others before
it reads them. The callee's return loads the
returned words into registers and frees the frame, and the caller stores them into its own
locations. x64 returns up to eight words in `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`, `r9` and
`r10`. arm64 returns up to fourteen in `x0` to `x13`.

A register location is a frame slot that register allocation has placed in a machine register.
The preserved ones are `rbx`, `rbp` and `r12` to `r15` on x64 and `x19` to `x28` on arm64, which
nothing else uses, and they are saved through the callee's frame. The caller-saved ones are
`r8`, `r9`, `r10`, `rdi`, `rsi` and `rdx` on x64 and `x4` to `x7`, `x10` to `x14`, `x8` and `x3`
`x0` to `x3` on arm64. A call destroys them all; an extern call destroys `rdi rsi rdx` on x64 (its
arguments) and `x8`, `x0` to `x2` on arm64 (its number, arguments and result); a division
destroys `rdx` and a remainder `rdi rsi rdx` on x64. Each holds only values live across no
instruction that destroys it (`Live.clobOk` over the clobber set `cls`). A `ret` loads the
result registers, the caller moves the results into their locations and a `write` or `read` of a
buffer sets its argument registers each by one parallel move (`Sel.PMove.seq`, through `r11` or
`rcx` on x64 and `x16` or `x17` on arm64), so an operand may sit in any argument or result register
and a result may stay in the register it arrives in.
They are never saved, so they have no frame word: slot `x` of a frame is its word `x - c`
(`Sel.frameW`). A
callee's caller-saved locations receive their arguments in registers, by a parallel move
through a temporary (`rax`, `x9`). With caller-saved locations a function returns at most five
words on x64 and four on arm64. Before a call, the
caller stores each register the callee may use into the matching word of the callee's frame,
which the callee leaves free for this purpose, and the callee's return restores them. The caller
skips a register whose value is dead after the call, unless the register belongs to a deeper
activation or holds an argument; the restore of a skipped register loads a value nobody reads. A frame
therefore does not grow when registers are used, and the stack bound is no larger with registers
than without: the linker reserves `P.stackBytes (φ.words k c)`, which charges each frame only its
words, and register allocation compares frames in words (`RegAlloc.frameOk`). The scratch
registers every block uses hold no location (x64 `rax rcx`, arm64 `x9`, `x15` to `x17`), nor does
`r11`, which `syscall` destroys on hardware but not under qemu. The register `x18`
is never used, because Apple platforms reserve it.

## Cost and frame models

Each target supplies a cost model `κ`, which gives the number of instructions allowed for each
kind of source construct, and a frame model `φ`, which gives the bytes of stack occupied by a
call with `w` frame slots. On x64 a frame takes `8(w + 1)` bytes, the slots and the return
address. On arm64 it takes the slots and the saved `x30`, rounded as described above. The
compiler checks each program's selected code against `κ`, and the frame model enters the stack
bound by a theorem. Both are described in [resources.md](resources.md).

## Object formats and loaders

A format has a writer, which turns a linked image into the bytes of a file, and a loader model,
which says what the operating system does with such a file. Three formats are built. Static
ELF64 is the Linux format, which both targets use. PE32+ for x64 Windows and Mach-O for arm64
macOS are built as formats only, and no target uses them yet. The ELF
writer emits an ELF header, one `PT_LOAD` program header per segment, and a `PT_GNU_STACK`
header whose size is the stack the program needs and whose flags make the stack readable,
writable and not executable. The file has no section headers.

The loader model is a Lean function from bytes to the initial machine state. It is stricter than
the kernel, because it accepts only files of the shape the writer produces, and for such a file it
gives the memory the kernel would map: the bytes of each segment followed by zeros, with page
permissions from the segment's flags, a stack of the requested size below the stack top, and
the entry registers. Each format proves two laws. The writer refuses an image that is not
valid, and loading the written bytes gives exactly the image's initial state.

An image has up to three segments, each with one set of permissions: code that is readable and
executable, constants that are only readable, and the static data that is readable and writable.
No page is both writable and executable, so code never changes. The text starts at `0x400000` on
both targets. x64 lays out segments in pages of 4 KiB. arm64 lays them out in pages of 64 KiB
and pads each code and constant segment in the file to a whole page, so that kernels with 4, 16
or 64 KiB pages all map the same bytes. The writable segment comes last, and its trailing zeros
are left out of the file, since every kernel fills them with zeros.

A PE32+ file is a console executable whose image base is the page before the first segment, so
the segments must follow each other without a gap from there, and the base must be a multiple of
64 KiB. Windows has no stable system-call numbers, so the writer adds a read-only import section
after the last segment that imports a fixed list of functions from one DLL. The loader fills the
import address table of that section with the address of each function. The file has no base
relocations because the code is position-independent, and its stack reserve equals its commit,
so the whole stack is mapped when the program starts.

The PE loader model checks every header field. The varying ones, which are the entry point, the
image base, the image and header sizes, the stack size, the section table, and the import and
import address table directories, are checked against the sections and imports the model reads.
The fixed ones, which include the machine, the PE32+ magic, the section and file alignment, the
console subsystem, the DLL characteristics and the empty data directories, must hold exactly the
values the writer writes, so the laws alone cannot show that those values are right. Tests
compare them with the offsets of the PE/COFF specification and with files that lld-link makes.
The model ignores the section names, the hints of the import names and the bytes of the import
address table in the file, because Windows ignores them too. `load` leaves the headers and the
import section unmapped, so it gives exactly the image's initial state, and a second model also
maps them and fills the address table, with each slot proved to hold its function's address on a
read-only page. No file has run on Windows. The files run under wine, whose loader accepts files
that Windows refuses, so a run under wine shows only that the code does what it should.

The Mach-O format is a position-independent executable for arm64 macOS. macOS runs no fully static
executable, so the file names dyld as its dynamic linker and imports libSystem without binding any
symbol from it, and the program makes raw system calls. The writer puts the header in a page of its
own and each segment in whole 16 KiB pages above a 4 GiB `__PAGEZERO`, and it ends the file with an
ad-hoc code signature that holds the SHA-256 hash of every 4 KiB page before it. `LC_MAIN` gives the
entry point and a stack size that adds 512 KiB for dyld and the arguments to what the image asks
for.

The Mach-O loader model accepts only files of exactly this shape. It checks the header, the order
and contents of the load commands, each segment's protections, alignment, file range and single
section, the entry point inside `__TEXT`, and the signature, whose page hashes it recomputes from
the file's bytes. It is stricter than macOS, which checks a page's hash only when the page is
first touched and runs a file with a trailing byte after the signature. The model ignores the
contents of `LC_UUID` and of the header page after the commands, and it places the program at the
addresses in the file, while macOS slides it. The good files ran as expected on an arm64 Mac.
Corrupted files with a recomputed signature were run there too. macOS refused those with a wrong
magic, processor type, dyld path, command count, PIE flag, `__PAGEZERO` size, data alignment or
overlap, or text file offset, and a file with too small a stack crashed. It ran files with a
section outside its segment, a wrong `sizeofcmds`, an executable read-only segment or a writable
text segment, all of which the model refuses.

Every target that runs on Linux can also write its object as an ELF64 relocatable object, a `.o`
file that a system linker links with other objects. The file holds the object's sections, with
code as `SHT_PROGBITS` that is allocated and executable and zero-initialised data as
`SHT_NOBITS`, a symbol table with the local symbols first, an undefined global symbol for every
name that a relocation uses and the object does not define, and one `SHT_RELA` section for the
relocations of each section. Each relocation kind has the type of the processor supplement:
`pc32` is `R_X86_64_PC32` or `R_AARCH64_PREL32`, `abs64` is `R_X86_64_64` or `R_AARCH64_ABS64`,
and the arm64 fixups are `CALL26`, `CONDBR19`, `ADR_PREL_LO21`, `ADR_PREL_PG_HI21`,
`ADD_ABS_LO12_NC` and the `LDST` forms of `ABS_LO12_NC`. A section's name must fit its kind,
such as `.text` or `.text.hot` for code, because a system linker places a section by its name.

A reader model, written from the gABI and the processor supplements, turns such a file back into
an object, and it refuses most objects that a C compiler makes, whose relocations name section
symbols. It reads the file the writer made as the original object with its local symbols listed
first, and that order does not change what Millipede's linker does, so linking the objects read
back from the files gives the same image as linking the originals. The object of a program is
the one its executable is linked from, which is proved. What a system linker does with the file
is not modelled and no theorem covers a program it links. Tests link the objects of three
programs with GNU ld and ld.lld on both machines and compare the programs' behaviour with
Millipede's own executables, and they link Millipede code with C objects. Compiled code cannot
call C or be called from C yet, because its calling convention differs from C's, so only the
entry symbol can be called from C.

## Adding a target

A third target needs a `Target` value and a backend. The target needs an ISA model with its
laws, a system-call model, a format with its laws, a cost model and a frame model. The backend
needs a selector that gives the block of each Lin instruction and the entry sequence of each
function, a proof that each block simulates its Lin instruction, the instruction counts that
the budget check uses, an assembler with its laws, and linker settings. Nothing before
instruction selection changes. Once the backend proves its laws, the shared composition gives
the correctness theorem for the new target.

## Planned

The design calls for the C calling conventions of each platform, calls to and from C, Mach-O and PE
executables, relocatable objects for a system linker, and macOS and Windows targets. Of these the
PE32+ and Mach-O formats are built, and no target uses them, and ELF relocatable objects are
built for the two Linux targets, with no driver option that writes them. See [../roadmap.md](../roadmap.md) and
[deviations.md](deviations.md).

## Where this lives

| item | location |
|---|---|
| `Target`, `Machine.run` | Millipede/Target/Target.lean |
| `Isa`, `Isa.Laws` | Millipede/Target/Isa.lean |
| `Abi`, `Abi.linux` | Millipede/Target/Abi.lean |
| x64: `X64.isa`, `X64.linux`, `X64.κ`, `X64.φ`, selection | Millipede/Target/X64/ |
| arm64: `A64.isa`, `A64.linux`, `A64.κ`, `A64.φ` | Millipede/Target/A64/ |
| arm64 selector with register locations | Millipede/RegAlloc/A64Reg.lean |
| `x64Linux`, `arm64Linux`, `backends` | Millipede/Top/Compile.lean |
| `Format`, ELF writer and loader model | Millipede/Object/Format.lean, Millipede/Object/Elf/ |
| PE32+ writer and loader model, `Pe.win64` | Millipede/Object/Pe/ |
| Mach-O writer, loader model and SHA-256 | Millipede/Object/MachO/ |
| `Image`, `link` | Millipede/Object/Image.lean, Link.lean |
| ELF relocatable objects, `Compile.objects` | Millipede/Object/ElfRel/ |
