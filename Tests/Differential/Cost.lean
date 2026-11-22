import Tests.Differential.PtrFuncs

/-!
# Cost regression for borrows

On the machine a reference is a pointer and a slice is a pointer and a length. Borrowing a struct
or a window of an array, passing it to a function and stepping a reactor's root therefore cost
the same number of instructions whatever the size, while passing a struct by value copies it at
a cost in proportion to its size. A compiler that copied a borrowed value in and out would give
the same results, so the functional differential tests cannot see it, and this suite guards
against it.

`differential cost <dir>` compiles programs that do one operation 2 times or 6 times and exit
with a status computed from the results. Each is built for a small and a large struct, of 4 and
64 words for the borrows and of 8 and 64 words for the loops. The operations are these:
* `mut` and `shr` call `touch (&mut s)` and `peek (&s)`;
* `bmut` and `bshr` are the scoped borrows `let r := &mut s` and `let r := &s`;
* `slm` and `sls` are the scoped slice borrows `&mut s.items[1:hi]` and `&s.items[1:hi]`, of 2
  words for the small struct and 60 for the large one;
* `sla` and `slma` pass the same windows as slice arguments to `peekS` and `touchS`;
* `root` steps a reactor whose root is the struct, 3 or 7 times;
* `lpm`, `lps` and `lpr` are loops of 2 or 6 iterations whose callee fills a `&mut` slice window,
  sums a shared window, or updates two fields of the `&mut` struct;
* `val` and `lpv` are the controls, which pass the struct by value in a call or in a loop body.

`scripts/differential.sh` runs the programs under qemu with one trace line per executed
instruction and checks each exit status. It requires that the extra instructions of 4 more
operations, in which the construction of the struct cancels out, are the same for the small and
the large struct for every kind but the controls. To show that the measurement is sensitive, it
also requires passing by value to cost more for the large struct.
-/

namespace Millipede.Tests.Differential

open Millipede

-- These functions are only compiled and measured, so `mp def` makes no attempt at their
-- obligations.
set_option mp.autoSafe false

set_option hygiene false in
/-- The programs of one size. They are a struct `<tag>Big` of `n` words, the callees `touch`, `peek`
and `take`, which take it by `&mut`, by `&` and by value, and the programs that call each 2 and 6
times. -/
macro "mp_cost " tag:ident n:num hi:num : command => do
  let nm (s : String) := Lean.mkIdentFrom tag (tag.getId.appendAfter s)
  let big := nm "Big"
  let sx := fun (s : String) => nm s
  let c1 ← `(structure $big where
      count : UInt64
      items : Vector UInt64 $n
    deriving Data, Inhabited)
  let c2 ← `(mp def $(sx "touch") (s : &mut $big) (d : UInt64) : Unit := do
      s.count := s.count + d
      s.items[1] := s.items[1] + d
      ())
  let c3 ← `(mp def $(sx "peek") (s : &$big) (d : UInt64) : UInt64 := s.count + s.items[1] + d)
  let c4 ← `(mp def $(sx "take") (s : $big) (d : UInt64) : UInt64 := s.count + s.items[1] + d)
  let c5 ← `(mp def $(sx "mut2") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(sx "touch") (&mut s) 1
      let _ := $(sx "touch") (&mut s) 2
      let _x := Examples.sysExit 0
      ())
  let c6 ← `(mp def $(sx "mut6") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(sx "touch") (&mut s) 1
      let _ := $(sx "touch") (&mut s) 2
      let _ := $(sx "touch") (&mut s) 3
      let _ := $(sx "touch") (&mut s) 4
      let _ := $(sx "touch") (&mut s) 5
      let _ := $(sx "touch") (&mut s) 6
      let _x := Examples.sysExit 0
      ())
  let c7 ← `(mp def $(sx "shr2") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(sx "peek") (&s) 1
      let b := $(sx "peek") (&s) a
      let _x := Examples.sysExit (a + b)
      ())
  let c8 ← `(mp def $(sx "shr6") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(sx "peek") (&s) 1
      let b := $(sx "peek") (&s) a
      let c := $(sx "peek") (&s) b
      let d := $(sx "peek") (&s) c
      let e := $(sx "peek") (&s) d
      let f := $(sx "peek") (&s) e
      let _x := Examples.sysExit (a + b + c + d + e + f)
      ())
  let c9 ← `(mp def $(sx "val2") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(sx "take") s 1
      let b := $(sx "take") s a
      let _x := Examples.sysExit (a + b)
      ())
  let c10 ← `(mp def $(sx "val6") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(sx "take") s 1
      let b := $(sx "take") s a
      let c := $(sx "take") s b
      let d := $(sx "take") s c
      let e := $(sx "take") s d
      let f := $(sx "take") s e
      let _x := Examples.sysExit (a + b + c + d + e + f)
      ())
  -- scoped borrows `let r := &mut s` and `let r := &s`, which elaborate to borrows instead of calls
  let c11 ← `(mp def $(sx "bmut2") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _x := Examples.sysExit s.count
      ())
  let c12 ← `(mp def $(sx "bmut6") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _ := (do let r := &mut s; r.count := r.count + 1; ())
      let _x := Examples.sysExit s.count
      ())
  let c13 ← `(mp def $(sx "bshr2") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := (let r := &s; r.count + r.items[1] + 1)
      let b := (let r := &s; r.count + r.items[1] + a)
      let _x := Examples.sysExit (a + b)
      ())
  let c14 ← `(mp def $(sx "bshr6") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := (let r := &s; r.count + r.items[1] + 1)
      let b := (let r := &s; r.count + r.items[1] + a)
      let c := (let r := &s; r.count + r.items[1] + b)
      let d := (let r := &s; r.count + r.items[1] + c)
      let e := (let r := &s; r.count + r.items[1] + d)
      let f := (let r := &s; r.count + r.items[1] + e)
      let _x := Examples.sysExit (a + b + c + d + e + f)
      ())
  -- slice borrows `&mut s.items[1:hi]` and `&s.items[1:hi]` of a window of `hi - 1` words
  let c15 ← `(mp def $(sx "slm2") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _x := Examples.sysExit s.items[1]
      ())
  let c16 ← `(mp def $(sx "slm6") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _ := (do let r := &mut s.items[1:$hi]; r[0]! := r[0]! + 1; ())
      let _x := Examples.sysExit s.items[1]
      ())
  let c17 ← `(mp def $(sx "sls2") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := (let r := &s.items[1:$hi]; r[0]! + r[1]! + 1)
      let b := (let r := &s.items[1:$hi]; r[0]! + r[1]! + a)
      let _x := Examples.sysExit (a + b)
      ())
  let c18 ← `(mp def $(sx "sls6") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := (let r := &s.items[1:$hi]; r[0]! + r[1]! + 1)
      let b := (let r := &s.items[1:$hi]; r[0]! + r[1]! + a)
      let c := (let r := &s.items[1:$hi]; r[0]! + r[1]! + b)
      let d := (let r := &s.items[1:$hi]; r[0]! + r[1]! + c)
      let e := (let r := &s.items[1:$hi]; r[0]! + r[1]! + d)
      let f := (let r := &s.items[1:$hi]; r[0]! + r[1]! + e)
      let _x := Examples.sysExit (a + b + c + d + e + f)
      ())
  -- slice arguments `f (&s.items[1..hi])` and `f (&mut s.items[1..hi])`, for which the callee gets
  -- a pointer and a length whatever the window's size
  let c24 ← `(mp def $(sx "peekS") (s : &[UInt64; $n]) requires 2 ≤ s.len.toNat : UInt64 := s[0] + s[1])
  let c25 ← `(mp def $(sx "touchS") (s : &mut [UInt64; $n]) requires 1 ≤ s.len.toNat : Unit := do
      s[0] := s[0] + 1
      ())
  let c26 ← `(mp def $(sx "sla2") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(sx "peekS") (&s.items[1..$hi]) + 1
      let b := $(sx "peekS") (&s.items[1..$hi]) + a
      let _x := Examples.sysExit (a + b)
      ())
  let c27 ← `(mp def $(sx "sla6") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(sx "peekS") (&s.items[1..$hi]) + 1
      let b := $(sx "peekS") (&s.items[1..$hi]) + a
      let c := $(sx "peekS") (&s.items[1..$hi]) + b
      let d := $(sx "peekS") (&s.items[1..$hi]) + c
      let e := $(sx "peekS") (&s.items[1..$hi]) + d
      let f := $(sx "peekS") (&s.items[1..$hi]) + e
      let _x := Examples.sysExit (a + b + c + d + e + f)
      ())
  let c28 ← `(mp def $(sx "slma2") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _x := Examples.sysExit s.items[1]
      ())
  let c29 ← `(mp def $(sx "slma6") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _ := $(sx "touchS") (&mut s.items[1..$hi])
      let _x := Examples.sysExit s.items[1]
      ())
  -- a reactor whose root is the struct; `init` builds it, each `step` takes it by `&mut` and bumps
  -- `count`, and the step that sees `count = k` exits, so `k + 1` steps run in all
  let c19 ← `(mp def $(sx "rinit") : $big := { count := 0, items := Vector.replicate $n 7 : $big })
  let c20 ← `(mp def $(sx "rstep2") (r : &mut $big) : Unit := do
      if r.count == 2 then
        let _x := Examples.sysExit r.count
        ()
      else
        r.count := r.count + 1
        ())
  let c21 ← `(mp def $(sx "rstep6") (r : &mut $big) : Unit := do
      if r.count == 6 then
        let _x := Examples.sysExit r.count
        ()
      else
        r.count := r.count + 1
        ())
  let c22 ← `(command| mp program $(sx "root2") (root : $big) init $(sx "rinit") step $(sx "rstep2"))
  let c23 ← `(command| mp program $(sx "root6") (root : $big) init $(sx "rinit") step $(sx "rstep6"))
  return ⟨Lean.mkNullNode (#[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15,
    c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29].map (·.raw))⟩

set_option hygiene false in
/-- The loop programs of one size, a struct `<tag>LBig` of `n` words and in-place loops over it that
run for 2 and for 6 iterations. In `lpm` a callee fills the `&mut` slice window `s.items[1..hi]`
in place, with `hi` 3 or 7, and in `lps` a callee sums a shared window. In `lpr` a callee loops
over the `&mut` struct and updates two of its fields. The control `lpv` passes the struct by value
to a callee in its loop body, so it copies the struct on every iteration. -/
macro "mp_lcost " tag:ident n:num : command => do
  let nm (s : String) := Lean.mkIdentFrom tag (tag.getId.appendAfter s)
  let big := nm "LBig"
  let c1 ← `(structure $big where
      count : UInt64
      items : Vector UInt64 $n
    deriving Data, Inhabited)
  let c2 ← `(mp def $(nm "lbump") (s : &mut [UInt64; $n]) : Unit := do
      for i in 0...s.len do
        s[i] := s[i] + 1
        ())
  let c3 ← `(mp def $(nm "lsum") (s : &[UInt64; $n]) : UInt64 := do
      let mut acc := 0
      for i in 0...s.len do
        acc := acc + s[i]
      acc)
  let c4 ← `(mp def $(nm "lgrow") (s : &mut $big) (k : UInt64) : Unit := do
      for i in 0...8 do
        if i ≥ k then break
        s.count := s.count + i + 1
        s.items[1] := s.items[1] + 1
        ())
  let c5 ← `(mp def $(nm "ltake") (s : $big) (d : UInt64) : UInt64 := s.count + s.items[1] + d)
  let c6 ← `(mp def $(nm "lpm2") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(nm "lbump") (&mut s.items[1..3])
      let _x := Examples.sysExit (s.items[2] + s.items[6] * 2)
      ())
  let c7 ← `(mp def $(nm "lpm6") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(nm "lbump") (&mut s.items[1..7])
      let _x := Examples.sysExit (s.items[2] + s.items[6] * 2)
      ())
  let c8 ← `(mp def $(nm "lps2") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(nm "lsum") (&s.items[1..3])
      let _x := Examples.sysExit a
      ())
  let c9 ← `(mp def $(nm "lps6") : Unit :=
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let a := $(nm "lsum") (&s.items[1..7])
      let _x := Examples.sysExit a
      ())
  let c10 ← `(mp def $(nm "lpr2") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(nm "lgrow") (&mut s) 2
      let _x := Examples.sysExit (s.count + s.items[1])
      ())
  let c11 ← `(mp def $(nm "lpr6") : Unit := do
      let mut s := { count := 0, items := Vector.replicate $n 7 : $big }
      let _ := $(nm "lgrow") (&mut s) 6
      let _x := Examples.sysExit (s.count + s.items[1])
      ())
  let c12 ← `(mp def $(nm "lpv2") : Unit := do
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let mut a := 0
      for i in 0...2 do
        a := a + $(nm "ltake") s i
      let _x := Examples.sysExit a
      ())
  let c13 ← `(mp def $(nm "lpv6") : Unit := do
      let s := { count := 0, items := Vector.replicate $n 7 : $big }
      let mut a := 0
      for i in 0...6 do
        a := a + $(nm "ltake") s i
      let _x := Examples.sysExit a
      ())
  return ⟨Lean.mkNullNode (#[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13].map (·.raw))⟩

-- the automatic attempt at the bounds obligations of six slice borrows recurses deeply; it fails
-- to discharge them, and `compile` does not need them
set_option maxRecDepth 8192

mp_cost cs 4 3
mp_cost cl 64 61
mp_lcost cs2 8
mp_lcost cl2 64

/-- The cost programs with their file tags. Each program exits from its last step. A tag is
`<size>-<kind><count>`, where the size is `s` for the small struct and `l` for the large one, the
kind is one of those of the module documentation, and the count is 2 or 6 operations, or loop
iterations for the loop kinds. -/
def costProgs : List (String × Program) :=
  let mk (init : Exp [] Ty.unit) : Program := ⟨Ty.unit, init, Examples.keepUnit.exp⟩
  [("s-mut2", mk csmut2.exp), ("s-mut6", mk csmut6.exp), ("s-shr2", mk csshr2.exp),
   ("s-shr6", mk csshr6.exp), ("s-val2", mk csval2.exp), ("s-val6", mk csval6.exp),
   ("s-bmut2", mk csbmut2.exp), ("s-bmut6", mk csbmut6.exp), ("s-bshr2", mk csbshr2.exp),
   ("s-bshr6", mk csbshr6.exp), ("s-slm2", mk csslm2.exp), ("s-slm6", mk csslm6.exp),
   ("s-sls2", mk cssls2.exp), ("s-sls6", mk cssls6.exp), ("s-root2", csroot2),
   ("s-root6", csroot6), ("s-sla2", mk cssla2.exp), ("s-sla6", mk cssla6.exp),
   ("s-slma2", mk csslma2.exp), ("s-slma6", mk csslma6.exp),
   ("s-lpm2", mk cs2lpm2.exp), ("s-lpm6", mk cs2lpm6.exp), ("s-lps2", mk cs2lps2.exp),
   ("s-lps6", mk cs2lps6.exp), ("s-lpr2", mk cs2lpr2.exp), ("s-lpr6", mk cs2lpr6.exp),
   ("s-lpv2", mk cs2lpv2.exp), ("s-lpv6", mk cs2lpv6.exp),
   ("l-mut2", mk clmut2.exp), ("l-mut6", mk clmut6.exp), ("l-shr2", mk clshr2.exp),
   ("l-shr6", mk clshr6.exp), ("l-val2", mk clval2.exp), ("l-val6", mk clval6.exp),
   ("l-bmut2", mk clbmut2.exp), ("l-bmut6", mk clbmut6.exp), ("l-bshr2", mk clbshr2.exp),
   ("l-bshr6", mk clbshr6.exp), ("l-slm2", mk clslm2.exp), ("l-slm6", mk clslm6.exp),
   ("l-sls2", mk clsls2.exp), ("l-sls6", mk clsls6.exp), ("l-root2", clroot2),
   ("l-root6", clroot6), ("l-sla2", mk clsla2.exp), ("l-sla6", mk clsla6.exp),
   ("l-slma2", mk clslma2.exp), ("l-slma6", mk clslma6.exp),
   ("l-lpm2", mk cl2lpm2.exp), ("l-lpm6", mk cl2lpm6.exp), ("l-lps2", mk cl2lps2.exp),
   ("l-lps6", mk cl2lps6.exp), ("l-lpr2", mk cl2lpr2.exp), ("l-lpr6", mk cl2lpr6.exp),
   ("l-lpv2", mk cl2lpv2.exp), ("l-lpv6", mk cl2lpv6.exp)]

end Millipede.Tests.Differential
