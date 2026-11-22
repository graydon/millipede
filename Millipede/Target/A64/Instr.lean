/-!
# The modelled arm64 instruction subset

The subset holds what instruction selection needs for Lin. It has moves of 64-bit constants by
`movz`, `movk` and `movn`, loads and stores of every width with base and offset addressing, and
the arithmetic, logical, shift, multiply and divide operations of `Flat.BinOp`, with the
remainder computed by `msub`. A comparison is a `subs` into `xzr` followed by `csinc`, which is
`cset`. The subset also has conditional and unconditional branches, `bl` and `ret`, the system
call `svc` and the pc-relative addresses `adr` and `adrp`, but no indirect branch other than
`ret`, since nothing selects `br` or `blr`. Every data-processing instruction comes in a 64-bit
form with `sf = true` on the `X` registers, and a 32-bit form on the `W` registers whose result is
zero-extended into the 64-bit register.

The constructors, their canonical assembly and some of the aliases they cover are the following:

| constructor | assembly (canonical, no aliases) | alias examples |
|---|---|---|
| `mov .z/.n/.k sf d imm hw` | `movz/movn/movk d, #imm, lsl #(16 hw)` | `mov` |
| `addImm sf sub setf d n imm sh` | `add/adds/sub/subs d, n, #imm{, lsl #12}` | `cmp`, `cmn`, `mov` to/from `sp` |
| `addReg sf sub setf d n m` | `add/adds/sub/subs d, n, m` (shifted register, `lsl #0`) | `cmp`, `neg` |
| `logReg op sf d n m` | `and/orr/eor/ands d, n, m` (shifted register, `lsl #0`) | `mov`, `tst` |
| `madd sf sub d n m a` | `madd/msub d, n, m, a` | `mul`, `mneg` |
| `div sf signed d n m` | `udiv/sdiv d, n, m` | |
| `shiftV op sf d n m` | `lslv/lsrv/asrv/rorv d, n, m` | `lsl/lsr/asr/ror` |
| `bfm signed sf d n immr imms` | `sbfm/ubfm d, n, #immr, #imms` | `lsl/lsr/asr #k`, `sxtb/uxtb…`, `ubfx` |
| `csel op sf d n m c` | `csel/csinc/csinv/csneg d, n, m, c` | `cset`, `csetm`, `cinc` |
| `ldr sz t a` / `str sz t a` | `ldr/ldrb/ldrh` (zero-extending), `str/strb/strh` | |
| `adr page d imm` | `adr d, pc + imm` / `adrp d, page(pc) + 4096 imm` | |
| `b link imm` | `b/bl pc + 4 imm` | |
| `bcond c imm` | `b.c pc + 4 imm` | |
| `cbz sf nz t imm` | `cbz/cbnz t, pc + 4 imm` | |
| `ret n` | `ret n` | |
| `svc imm` | `svc #imm` | |

An address `uimm n imm` is `[n, #imm * size]`, an unsigned 12-bit offset scaled by the access
size. An address `simm n imm` is `[n, #simm9]`, the signed and unscaled 9-bit byte offset of
`ldur` and `stur`, and `reg n m` is `[n, m]`, a register offset with no extension or shift. There
are no writeback forms.

A register field is a 5-bit number, and number 31 means the stack pointer `sp` in some positions
and the zero register `xzr` in others, exactly as in the architecture. It is `sp` as the base of
an address, as both operands of an `add` or `sub` immediate that does not set flags, and as the
first operand of one that does. It is `xzr` everywhere else, which includes the destination of
`adds` and `subs` immediate, every register of the shifted-register forms, `madd`, `div`, the
shifts, `bfm`, `csel` and `movz`, the data register of a load or store, `cbz`, `ret` and the
register offset of an address.

Immediates are stored at their encoded width, so almost every instruction is encodable. The
exceptions are the 32-bit forms that the architecture leaves unallocated, which are the moves with
`hw ≥ 2` and `sbfm` or `ubfm` with `immr` or `imms` of 32 or more. The bitmask immediates of
`and`, `orr` and `eor` are not in the subset, since constants are built with `movz`, `movk` and
`movn` and then combined by register.

The subset also leaves out the extended-register forms, shifted operands other than `lsl #0`,
writeback addressing, sign-extending loads, whose work `sbfm` covers, load and store pairs,
flag-setting conditional compares, SIMD and floating point, and every system instruction other
than `svc`.
-/

namespace Millipede.A64

/-- A register field, which names `x0` to `x30` or number 31, `sp` or `xzr` by position. -/
abbrev Reg := BitVec 5

namespace Reg
/-- The link register `x30`. -/
def lr : Reg := 30
/-- Register number 31 where it means the stack pointer. -/
def sp : Reg := 31
end Reg

/-- The wide-immediate moves, where `movn` inverts, `movz` zeroes the other bits and `movk`
keeps them. -/
inductive MovOp
  | n | z | k
deriving DecidableEq, Repr, Inhabited

/-- The logical operations of the shifted-register form, of which `ands` sets the flags. -/
inductive LogOp
  | and | orr | eor | ands
deriving DecidableEq, Repr, Inhabited

/-- The shifts by a register, which take the amount modulo the width. -/
inductive ShiftOp
  | lsl | lsr | asr | ror
deriving DecidableEq, Repr, Inhabited

/-- The conditional selects `d := c ? n : f(m)`, where `f` is the identity, `+1`, `~` or
negation. -/
inductive CselOp
  | csel | csinc | csinv | csneg
deriving DecidableEq, Repr, Inhabited

/-- The access sizes of 1, 2, 4 and 8 bytes. -/
inductive Size
  | b | h | w | x
deriving DecidableEq, Repr, Inhabited

/-- The bytes an access of this size covers. -/
def Size.bytes : Size → Nat
  | .b => 1 | .h => 2 | .w => 4 | .x => 8

/-- The condition codes in encoding order, where `al` and `nv` both always hold. -/
inductive Cond
  | eq | ne | cs | cc | mi | pl | vs | vc | hi | ls | ge | lt | gt | le | al | nv
deriving DecidableEq, Repr, Inhabited

/-- All condition codes. -/
def Cond.all : List Cond := [.eq, .ne, .cs, .cc, .mi, .pl, .vs, .vc, .hi, .ls, .ge, .lt, .gt, .le, .al, .nv]

/-- An address of a load or store. -/
inductive Addr
  /-- `[n, #imm * size]`. -/
  | uimm (n : Reg) (imm : BitVec 12)
  /-- `[n, #sext imm]`, unscaled. -/
  | simm (n : Reg) (imm : BitVec 9)
  /-- `[n, m]`. -/
  | reg (n m : Reg)
deriving DecidableEq, Repr, Inhabited

/-- The modelled arm64 instructions. -/
inductive Instr
  | mov (op : MovOp) (sf : Bool) (d : Reg) (imm : BitVec 16) (hw : BitVec 2)
  | addImm (sf sub setf : Bool) (d n : Reg) (imm : BitVec 12) (lsl12 : Bool)
  | addReg (sf sub setf : Bool) (d n m : Reg)
  | logReg (op : LogOp) (sf : Bool) (d n m : Reg)
  | madd (sf sub : Bool) (d n m a : Reg)
  | div (sf signed : Bool) (d n m : Reg)
  | shiftV (op : ShiftOp) (sf : Bool) (d n m : Reg)
  | bfm (signed sf : Bool) (d n : Reg) (immr imms : BitVec 6)
  | csel (op : CselOp) (sf : Bool) (d n m : Reg) (c : Cond)
  | ldr (sz : Size) (t : Reg) (a : Addr)
  | str (sz : Size) (t : Reg) (a : Addr)
  | adr (page : Bool) (d : Reg) (imm : BitVec 21)
  | b (link : Bool) (imm : BitVec 26)
  | bcond (c : Cond) (imm : BitVec 19)
  | cbz (sf nz : Bool) (t : Reg) (imm : BitVec 19)
  | ret (n : Reg)
  | svc (imm : BitVec 16)
deriving DecidableEq, Repr, Inhabited

/-- Whether an instruction is encodable, which fails only for the 32-bit forms that the
architecture leaves unallocated. -/
def Instr.valid : Instr → Bool
  | .mov _ sf _ _ hw => sf || hw.msb == false
  | .bfm _ sf _ _ immr imms => sf || (immr.msb == false && imms.msb == false)
  | _ => true

end Millipede.A64
