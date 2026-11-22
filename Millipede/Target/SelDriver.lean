import Millipede.Compile.Asm
import Millipede.Compile.Lin
import Millipede.RegAlloc.Lock

/-!
# The selection driver

Every backend selects a Lin program the same way. Each function `i` becomes an Asm function
named `fnSym i`, whose entry sequence sets up its frame and whose block `pc` is the code of Lin
instruction `pc`. The data items the blocks need are collected, and the data region becomes the
zero-initialised writable region `mp_mem`. An ISA supplies a `Selector`, which gives the block of
one Lin instruction, the entry sequence and the functions it can select. `select_spec` describes
what `select D P` produces, and both ISAs' selections are instances of it.
-/

namespace Millipede.Sel

/-- The symbol of Lin function number `i`. -/
def fnSym (i : Nat) : String := "mp_f" ++ toString i

/-- The symbol of the constant buffer of the extern call at position `pc` of function `i`. -/
def dataSym (i pc : Nat) : String := "mp_d" ++ toString i ++ "_" ++ toString pc

/-- The symbol of the data region, the `M` bytes of a Lin program with `mem = M`. -/
def memSym : String := "mp_mem"

/-- What an ISA supplies to the driver. -/
structure Selector (A : Asm.Arch) where
  /-- The block of the Lin instruction at position `pc` of function `i`, whose code is `fn`, and
  its data. -/
  instr : Lin.Prog → Nat → Nat → Lin.Fn → Lin.Instr →
    Except String (List A.SInstr × List (String × List UInt8))
  /-- The entry sequence of a function. -/
  entry : Lin.Fn → List A.SInstr
  /-- The functions the ISA can select, within its limits on frames and returned words. -/
  fnOk : Lin.Fn → Bool

variable {A : Asm.Arch} (D : Selector A)

/-- Selects the blocks of a code list starting at position `pc`, by structural recursion on the
code. -/
def selCode (P : Lin.Prog) (i : Nat) (fn : Lin.Fn) :
    Nat → List Lin.Instr → Except String (List (List A.SInstr) × List (String × List UInt8))
  | _, [] => .ok ([], [])
  | pc, ins :: rest => do
    let (b, d) ← D.instr P i pc fn ins
    let (bs, ds) ← selCode P i fn (pc + 1) rest
    pure (b :: bs, d ++ ds)

/-- Selects function number `i`. -/
def selFn (P : Lin.Prog) (i : Nat) (fn : Lin.Fn) :
    Except String (Asm.Fn A × List (String × List UInt8)) :=
  if D.fnOk fn then do
    let (bs, ds) ← selCode D P i fn 0 fn.code
    pure (⟨fnSym i, D.entry fn, bs⟩, ds)
  else .error ("select: frame or return too large in " ++ fn.name)

/-- Selects the functions from number `i` on, by structural recursion on the list. -/
def selFns (P : Lin.Prog) :
    Nat → List Lin.Fn → Except String (List (Asm.Fn A) × List (String × List UInt8))
  | _, [] => .ok ([], [])
  | i, fn :: fs => do
    let (f, d) ← selFn D P i fn
    let (rest, ds) ← selFns P (i + 1) fs
    pure (f :: rest, d ++ ds)

/-- Instruction selection with the selector `D`. -/
def select (P : Lin.Prog) : Except String (Asm.Prog A) := do
  if P.main < P.funs.length then
    let (fs, ds) ← selFns D P 0 P.funs
    pure { funs := fs, data := ds, main := P.main, bss := [(memSym, P.mem)] }
  else .error "select: no main function"

/-! ## The shape of selected code -/

variable {D} {P : Lin.Prog}

theorem selCode_spec {i : Nat} {fn : Lin.Fn} : ∀ (code : List Lin.Instr) (pc0 : Nat)
    (bs : List (List A.SInstr)) (ds : List (String × List UInt8)),
    selCode D P i fn pc0 code = .ok (bs, ds) → bs.length = code.length ∧
      ∀ k ins, code[k]? = some ins → ∃ b d, bs[k]? = some b ∧
        D.instr P i (pc0 + k) fn ins = .ok (b, d) ∧ ∀ x ∈ d, x ∈ ds
  | [], _, bs, ds, h => by cases h; exact ⟨rfl, fun k ins h => by simp at h⟩
  | ins :: code, pc0, bs, ds, h => by
    simp only [selCode, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p hp
      obtain ⟨b, d⟩ := p
      split at h
      · cases h
      · rename_i q hq
        obtain ⟨bs', ds'⟩ := q
        cases h
        obtain ⟨hl, hk⟩ := selCode_spec code (pc0 + 1) bs' ds' hq
        refine ⟨by simp [hl], fun k ins' hk' => ?_⟩
        cases k with
        | zero =>
          cases hk'
          exact ⟨b, d, rfl, by simpa using hp, fun x hx => List.mem_append_left _ hx⟩
        | succ k =>
          obtain ⟨b', d', h1, h2, h3⟩ := hk k ins' (by simpa using hk')
          refine ⟨b', d', by simpa using h1,
            (by rw [show pc0 + (k + 1) = pc0 + 1 + k by omega]; exact h2),
            fun x hx => List.mem_append_right _ (h3 x hx)⟩

variable (D) in
/-- What `select` produced for function `i`. -/
structure SelFn (P : Lin.Prog) (i : Nat) (fn : Lin.Fn) (f : Asm.Fn A)
    (ds : List (String × List UInt8)) : Prop where
  ok : D.fnOk fn = true
  name : f.name = fnSym i
  entry : f.entry = D.entry fn
  code : ∃ d, selCode D P i fn 0 fn.code = .ok (f.blocks, d) ∧ ∀ x ∈ d, x ∈ ds

theorem selFns_spec : ∀ (fs : List Lin.Fn) (i0 : Nat) (afs : List (Asm.Fn A))
    (ds : List (String × List UInt8)), selFns D P i0 fs = .ok (afs, ds) →
    afs.length = fs.length ∧
      ∀ k fn, fs[k]? = some fn → ∃ f, afs[k]? = some f ∧ SelFn D P (i0 + k) fn f ds
  | [], _, afs, ds, h => by cases h; exact ⟨rfl, fun k fn h => by simp at h⟩
  | fn :: fs, i0, afs, ds, h => by
    simp only [selFns, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p hp
      obtain ⟨f, d⟩ := p
      split at h
      · cases h
      · rename_i q hq
        obtain ⟨rest, ds'⟩ := q
        cases h
        obtain ⟨hl, hk⟩ := selFns_spec fs (i0 + 1) rest ds' hq
        refine ⟨by simp [hl], fun k fn' hk' => ?_⟩
        cases k with
        | zero =>
          cases hk'
          simp only [selFn] at hp
          split at hp
          · rename_i hok
            simp only [bind, Except.bind] at hp
            split at hp
            · cases hp
            · rename_i r hr
              obtain ⟨bs, d'⟩ := r
              cases hp
              exact ⟨_, rfl, ⟨hok, by simp, rfl, ⟨d', by simpa using hr,
                fun x hx => List.mem_append_left _ hx⟩⟩⟩
          · cases hp
        | succ k =>
          obtain ⟨f', h1, h2⟩ := hk k fn' (by simpa using hk')
          refine ⟨f', by simpa using h1, ?_⟩
          rw [show i0 + (k + 1) = i0 + 1 + k by omega]
          exact ⟨h2.ok, h2.name, h2.entry, h2.code.elim fun d' ⟨hc, hd⟩ =>
            ⟨d', hc, fun x hx => List.mem_append_right _ (hd x hx)⟩⟩

/-- `select` keeps `main` and its index, and produces one Asm function for each Lin function,
as `SelFn` describes. -/
theorem select_spec {AP : Asm.Prog A} (h : select D P = .ok AP) :
    AP.main = P.main ∧ P.main < P.funs.length ∧ AP.funs.length = P.funs.length ∧
      ∀ k fn, P.funs[k]? = some fn → ∃ f, AP.funs[k]? = some f ∧ SelFn D P k fn f AP.data := by
  simp only [select, bind, Except.bind] at h
  split at h
  · rename_i hm
    split at h
    · cases h
    · rename_i q hq
      obtain ⟨fs, ds⟩ := q
      cases h
      obtain ⟨hl, hk⟩ := selFns_spec P.funs 0 fs ds hq
      exact ⟨rfl, hm, hl, fun k fn h => by simpa using hk k fn h⟩
  · cases h

/-- The only writable region of `select`'s output is the data region. -/
theorem select_bss {AP : Asm.Prog A} (h : select D P = .ok AP) : AP.bss = [(memSym, P.mem)] := by
  simp only [select, bind, Except.bind] at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · cases h

end Millipede.Sel
