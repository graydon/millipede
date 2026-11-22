import Millipede.Top.Compile
import Millipede.Object.ElfRel.Write

/-!
# Relocatable objects of a program

`Compile.objects p t` compiles program `p` for target `t` up to the assembler and writes the
object as an ELF relocatable file, which a system linker can link with other objects. The result
is a list of named files, which today holds the one object of the program, `prog.o`, because the
compiler assembles every function and data item into one `Obj`. `Compile.objLink` gives that
`Obj` with the settings Millipede's own linker uses for it, whose entry symbol a system linker
must also be given.

The object is that of the program `compileWith o` compiles: `compileRun` chooses the
configuration of Core passes, falling back to fewer passes when the pipeline refuses the
optimised program, and the object is assembled from the program that configuration gives.
`objLink_compileRun` proves that linking the object with `link` and writing the result in the
target's executable format gives exactly the bytes of the executable that `compileWith o`
returns. Nothing is proved about what a system linker makes of the object.
-/

namespace Millipede.Compile

/-- The pipeline of backend `B` up to the assembler, with the linker settings for its object. -/
def objOf (B : Backend) (p : Program) : Except String (Obj × Link.Config) := do
  if checks p = false then
    throw "compile: a term the borrow checker rejects, or a lens, constructor or split without a certificate of its law"
  let fp ← Flat.lower p
  let P := B.prep (Lin.linearize fp p.memBytes)
  let A ← B.select P
  if B.budgetOk P = false then throw B.budgetMsg
  let obj ← B.assemble A
  pure (obj, B.linkConfig P)

/-- The executable pipeline is the object pipeline followed by `link` and the format's writer. -/
theorem objOf_link (B : Backend) (p : Program) (obj : Obj) (cfg : Link.Config)
    (h : objOf B p = .ok (obj, cfg)) :
    bytesOf B p = (Link.link cfg [obj]).bind B.target.fmt.write := by
  unfold objOf at h
  unfold bytesOf backendOf
  cases hc : checks p <;> cases hl : Flat.lower p <;>
    simp only [hc, hl, ite_true, ite_false, bind, Except.bind, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at h ⊢
  rename_i fp
  cases hs : B.select (B.prep (Lin.linearize fp p.memBytes)) <;> simp only [hs, reduceCtorEq] at h ⊢
  cases hb : B.budgetOk (B.prep (Lin.linearize fp p.memBytes)) <;>
    simp only [hb, ite_true, ite_false, reduceCtorEq] at h ⊢
  rename_i A
  cases ha : B.assemble A <;> simp only [ha, reduceCtorEq, pure, Except.pure] at h ⊢
  cases h
  rfl

/-- The bytes of the program that `compileRun` chose are those of the pipeline on that
program. -/
theorem firstOk_bytesOf (B : Backend) (κ : CostModel) (φ : FrameModel) (p : Program) :
    ∀ (cs : List Opt.Config) (e : String) {bs : List UInt8} {c : Opt.Config},
      firstOk B κ φ p cs (.error e) = .ok (bs, c) → bytesOf B (c.optimize κ φ p) = .ok bs
  | [], _, _, _, h => by cases h
  | c' :: cs, _, bs, c, h => by
    simp only [firstOk] at h
    split at h
    · cases h; assumption
    · exact firstOk_bytesOf B κ φ p cs _ h

theorem compileRun_bytesOf {o : Options} {p : Program} {t : Target} {B : Backend}
    {bs : ByteArray} {c : Opt.Config} (hB : Backend.of? t o = some B)
    (h : compileRun o p t = .ok (bs, c)) :
    bytesOf B (c.optimize t.κ t.φ p) = .ok bs.data.toList := by
  unfold compileRun at h
  rw [hB] at h
  dsimp only at h
  split at h
  · cases hb : bytesOf B p <;> rw [hb] at h <;> cases h
    rw [Opt.Config.optimize_none, hb]
  · split at h
    · rename_i bs' hb; cases h; exact hb
    · split at h
      · cases hf : firstOk B t.κ t.φ p o.opt.prefixes (.error _) with
        | error => rw [hf] at h; cases h
        | ok r =>
          rw [hf] at h; cases h
          exact firstOk_bytesOf B t.κ t.φ p _ _ hf
      · cases h

/-- The object of `p` for target `t` with options `o` and its linker settings, assembled from
the program that `compileRun o p t` compiles. -/
def objLink (p : Program) (t : Target) (o : Options := {}) : Except String (Obj × Link.Config) :=
  match Backend.of? t o with
  | none => .error ("compile: unsupported target " ++ t.name)
  | some B => do
    let (_, c) ← compileRun o p t
    objOf B (c.optimize t.κ t.φ p)

/-- Linking the object of `objLink` with Millipede's linker and writing the image gives the
executable that `compileWith` returns. -/
theorem objLink_compileRun {o : Options} {p : Program} {t : Target} {B : Backend}
    {obj : Obj} {cfg : Link.Config} {bs : ByteArray} {c : Opt.Config}
    (hB : Backend.of? t o = some B) (hc : compileRun o p t = .ok (bs, c))
    (h : objLink p t o = .ok (obj, cfg)) :
    (Link.link cfg [obj]).bind B.target.fmt.write = .ok bs.data.toList := by
  unfold objLink at h
  rw [hB, hc] at h
  rw [← objOf_link B _ obj cfg h, compileRun_bytesOf hB hc]

/-- The ELF machine of a target, or `none` for a target without relocatable objects. -/
def relMach (t : Target) : Option ElfRel.Mach :=
  if t.name = x64Linux.name then some ElfRel.x64
  else if t.name = arm64Linux.name then some ElfRel.a64
  else none

/-- The relocatable object files of `p` for target `t`. -/
def objects (p : Program) (t : Target) (o : Options := {}) :
    Except String (List (String × ByteArray)) := do
  let (obj, _) ← objLink p t o
  match relMach t with
  | none => throw ("elfrel: no relocatable format for " ++ t.name)
  | some m =>
    let b ← ElfRel.writeByteArray m obj
    pure [("prog.o", b)]

end Millipede.Compile
