import Tests.FormatGen
import Millipede.Meta.Emit

/-!
# A program over the generated batch format

The program `batchEcho` reads its whole input (at most 256 bytes), then, one batch after another,
checks the batch with the generated validator `Batch.validAt`, reads it with `Batch.parseAt` and
writes it back with `Batch.writeAt`, so its output is the canonical bytes of each batch (the
skipped byte as zero). It exits with 0 at the end of the input, with 1 at a malformed batch, and
with 2 if the validator and the parser disagree, which their contracts exclude. Building this
file writes `.lake/batch-x64` and `.lake/batch-a64`, which `scripts/format-check.sh` runs against
a reference written in Python.
-/

namespace Millipede.Tests.FormatGen

open Millipede Millipede.Format Std.WP

set_option experimental.vcgen true

mp extern "read" bRead (fd : UInt64) (buf : &mut [U8]) : UInt64
mp extern "write" bWrite (fd : UInt64) (buf : &[U8]) : UInt64
mp extern noreturn "exit" bExit (code : UInt64) : UInt64

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- Check, read and write back the batch at `pos`: the result is the length of its canonical
bytes at the start of `out`, 0 when no batch is at `pos`, and 1 when the parser accepts a batch
that the validator rejects. -/
mp def echoOne (s : &[UInt8; 256]) (pos : &mut UInt64) (b : &mut Batch) (out : &mut [UInt8; 64])
    requires pos.toNat ≤ s.len.toNat ∧ batchFmt.maxSize ≤ out.len.toNat
    ensures result.toNat ≤ 51 ∧ (result ≠ 0 → pos'.toNat ≤ s.len.toNat) : UInt64 := do
  let mut q := pos
  let v := Batch.validAt (&s) (&mut q)
  let ok := Batch.parseAt (&s) (&mut pos) (&mut b)
  if !ok then return 0
  if !v then return 1
  let mut p : UInt64 := 0
  Batch.writeAt (&mut out) (&mut p) (&b)
  p

mp prove echoOne.safe := by
  fmt_safe [batchFmt_maxSize, Batch.Bound, Seq.Bound]

mp prove echoOne.spec := by
  intros
  vcgen [echoOne]
  all_goals fmt_norm
  all_goals try simp only [batchFmt_maxSize] at *
  all_goals fmt_close

/-- The program's root. -/
structure BRoot where
  inb : Arr UInt8 256
  inLen : UInt64
  pos : UInt64
  eof : UInt64
  b : Batch
  out : Arr UInt8 64
deriving Data

/-- The bounds the program keeps. -/
def BInv (r : BRoot) : Prop := r.inLen.toNat ≤ 256 ∧ r.pos.toNat ≤ r.inLen.toNat

/-- Read more input, until the end of the input or a full buffer. -/
mp def bFill (inb : &mut Arr UInt8 256) (inLen : &mut UInt64) (eof : &mut UInt64)
    requires inLen.toNat ≤ 256 ensures inLen.toNat ≤ inLen'.toNat ∧ inLen'.toNat ≤ 256 : Unit := do
  let n := inLen
  let k := bRead 0 (&mut inb[n..256])
  let stop := k == 0 || k > 256 -! n
  let m := if stop then n else n +! k
  inLen := m
  eof := if stop || m == 256 then 1 else eof

set_option mp.autoSafe false in
set_option mp.autoSpec false in
/-- One step: read until the input ends, then echo one batch. -/
mp def bStep (r : &mut BRoot) requires BInv r ensures BInv r' : Unit := do
  if r.eof == 0 then bFill (&mut r.inb) (&mut r.inLen) (&mut r.eof)
  else if r.pos == r.inLen then
    let _ := bExit 0
  else
    let n := r.inLen
    let m := echoOne (&r.inb[0..n]) (&mut r.pos) (&mut r.b) (&mut r.out[0..64])
    if m == 0 then
      r.pos := n
      let _ := bExit 1
    else if m == 1 then
      r.pos := n
      let _ := bExit 2
    else
      let _ := bWrite 1 (&r.out[0..m])

/-- The precondition of `echoOne` in a step. -/
theorem echo_pre {r : BRoot} (h : BInv r) :
    (r.pos.toNat ≤ r.inLen.toNat ∧ batchFmt.maxSize ≤ (64 : UInt64).toNat) ∧
      (r.inLen.toNat ≤ 256 ∧ ∀ k < r.inLen.toNat, (vview r.inb 0 r.inLen.toNat).isFull k = true) ∧
      (64 : UInt64).toNat ≤ 64 ∧ ∀ k < (64 : UInt64).toNat, (vview r.out 0 64).isFull k = true := by
  obtain ⟨hl, hp⟩ := h
  simp only [vview_isFull, UInt64.reduceToNat]
  exact ⟨⟨hp, by rw [batchFmt_maxSize]; decide⟩, ⟨hl, fun k hk => by simp; omega⟩, by decide, fun k hk => by simp; omega⟩

/-- An echoed batch fits the output buffer. -/
theorem echo_le {r : BRoot} (h : BInv r) :
    (echoOne (vview r.inb 0 r.inLen.toNat) r.inLen r.pos r.b (vview r.out 0 64) 64).run.fst.toNat ≤ 64 := by
  have := (echoOne.post (vview r.inb 0 r.inLen.toNat) r.inLen r.pos r.b (vview r.out 0 64) 64
    (echo_pre h)).1
  omega

mp prove bStep.safe := by
  mp_auto [echo_le]

mp prove bStep.spec := by
  intro ω r
  vcgen [bStep]
  all_goals try dsimp only at *
  case vc1 hinv _ => exact hinv.1
  case vc3 hinv _ _ => exact hinv
  case vc2 hinv _ _ _ inLen' _ _ _ hfill =>
    obtain ⟨-, hp⟩ := hinv
    exact ⟨hfill.2, show r.pos.toNat ≤ inLen'.toNat by omega⟩
  all_goals (
    have hinv : BInv r := by assumption
    have hh := echoOne.post _ r.inLen r.pos r.b _ 64 (echo_pre hinv)
    simp only [UInt64.sub_zero] at *
    generalize (echoOne (vview r.inb 0 r.inLen.toNat) r.inLen r.pos r.b (vview r.out 0 64) 64).run = R at *
    obtain ⟨n, out', b', pos', u⟩ := R
    obtain ⟨-, hpos'⟩ := hh
    dsimp only at *
    refine ⟨hinv.1, ?_⟩
    first | exact hpos' ‹¬n = 0› | simp)

/-- An empty name. -/
mp def LBytes.empty8 : LBytes 8 := { len := 0, data := Vector.replicate 8 0 }

/-- An empty header. -/
mp def hdr0 : Hdr := { ver := 0, sender := Vector.replicate 4 0 }

/-- An empty item. -/
mp def item0 : Item := { kind := 0, num := 0, code := 0, name := LBytes.empty8 }

/-- An empty batch. -/
mp def batch0 : Batch := { hdr := hdr0, items := { len := 0, data := Vector.replicate 3 item0 } }

set_option mp.autoSpec false in
/-- The initial root. -/
mp def bInit ensures BInv result : BRoot :=
  { inb := Vector.replicate 256 0, inLen := 0, pos := 0, eof := 0,
    b := batch0,
    out := Vector.replicate 64 0 }

mp prove bInit.spec := by
  vcgen [bInit, LBytes.empty8, hdr0, item0, batch0]
  simp only [BInv]
  exact ⟨by decide, by decide⟩

set_option maxRecDepth 8192 in
mp program batchEcho (root : BRoot) init bInit step bStep invariant BInv
example : batchEcho.Safe := batchEcho.safe

#mp_compile batchEcho ".lake/batch-x64"
#mp_compile batchEcho ".lake/batch-a64" "arm64-linux"

end Millipede.Tests.FormatGen
