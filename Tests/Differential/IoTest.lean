import Millipede.Lib.ByteBuf
import Tests.Differential.Harness
import Tests.ByteBuf

/-!
# Differential test of reading, processing and writing with short reads

`ioProg` is a reactor over a `ByteBuf`. Each step forgets the bytes it holds, reads up to 16
bytes into the free space through a mutable slice passed to the extern, reverses the bytes it got
in place through slice arguments, and writes them. At the end of input it exits with 0, and on an
error with 1. Since each `read`'s bytes come out reversed, the output depends on how the input is
cut into reads. The driver of `scripts/differential.sh` makes the cut deterministic by writing one
block to a pipe and waiting for exactly the bytes that the reference `ioRef` predicts before it
writes the next. A block of at most 16 bytes is then returned by one `read`, and a longer one by
reads of 16 and the rest. The blocks are short on purpose, from single bytes through every size up
to 33, and hold edge bytes.

`differential io <dir>` writes `<dir>/io.elf` and `<dir>/io.script`, whose lines `I <hex>` and
`O <hex>` give each block and its expected output. `scripts/differential.sh` runs the driver on
it, and in its self-test also on ELFs built with a seeded bug in the pipeline.
-/

namespace Millipede.Tests.Differential

open Millipede Millipede.Lib

mp extern noreturn "exit" ioExit (code : UInt64) : UInt64

/-- Swap the first and the last cell of a slice. -/
mp def swapEnds (s : &mut [UInt8; 16]) requires 1 ≤ s.len.toNat : Unit := do
  let j := s.len - 1
  let a := s[0]
  let b := s[j]
  s[0] := b
  s[j] := a
  ()

set_option maxHeartbeats 4000000 in
set_option mp.autoSafe.maxHeartbeats 400000 in
/-- Reverse the first `r` bytes of the buffer in place. In eight nested stages the slice
`[k, r - k)` has its ends swapped while it holds at least two cells, and each stage passes a
different run-time window of the same array as a slice argument. -/
mp def rev16 (b : &mut ByteBuf 16) (r : UInt64) requires 1 ≤ r.toNat ∧ r.toNat ≤ 16 : Unit :=
  if 1 < r then
    let _ := swapEnds (&mut b.bytes[0..r - 0])
    if 3 < r then
      let _ := swapEnds (&mut b.bytes[1..r - 1])
      if 5 < r then
        let _ := swapEnds (&mut b.bytes[2..r - 2])
        if 7 < r then
          let _ := swapEnds (&mut b.bytes[3..r - 3])
          if 9 < r then
            let _ := swapEnds (&mut b.bytes[4..r - 4])
            if 11 < r then
              let _ := swapEnds (&mut b.bytes[5..r - 5])
              if 13 < r then
                let _ := swapEnds (&mut b.bytes[6..r - 6])
                if 15 < r then
                  let _ := swapEnds (&mut b.bytes[7..r - 7])
                  ()
                else ()
              else ()
            else ()
          else ()
        else ()
      else ()
    else ()
  else ()

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- One step, which reads into the free space, reverses what came in place through a slice and
writes it. -/
mp def ioStep (b : &mut ByteBuf 16) : Unit := do
  b.len := 0
  let r := ByteBuf.readFrom (&mut b) 0
  if r == 0 then
    let _x := ioExit 0
    ()
  else if r <= 16 then
    let _ := rev16 (&mut b) r
    b.len := r
    let _w := ByteBuf.writeTo (&b) 1
    ()
  else
    let _x := ioExit 1
    ()

mp prove ioStep.safe := by
  intro ω w b
  mp_safe [ioStep.exp, ByteBuf.readFrom.exp_denote, ByteBuf.readFrom.Safe', ByteBuf.writeTo.Safe',
    rev16.Safe', ByteBuf.readFrom.req, ByteBuf.writeTo.req, rev16.req]
    using ByteBuf.readFrom.Safe', ByteBuf.writeTo.Safe', rev16.Safe'
  all_goals simp_all [ByteBuf.Inv, UInt64.le_iff_toNat_le]

/-- The empty buffer. It is the body of `ByteBuf.new` at capacity 16, so the image is the one that
`init ByteBuf.new` would give. -/
mp def ioInit : ByteBuf 16 := { bytes := Vector.replicate 16 0, len := 0 }

set_option maxRecDepth 16384 in

mp program ioProg (root : ByteBuf 16) init ioInit step ioStep

example : ioProg.Safe := ioProg.safe

#guard (compile ioProg x64Linux).toBool

open Millipede.Tests.RevChunks in
-- the source trace: each chunk read comes out reversed
#guard written (ioProg.events (chunks [[1, 2, 3], [4], (List.range 16).map (·.toUInt8)]) 5) =
  [[3, 2, 1], [4], ((List.range 16).map (·.toUInt8)).reverse]

/-! ## The reference and the blocks -/

/-- The bytes the program writes for a block written at once, which it reads as pieces of 16 and
the rest and reverses piece by piece. -/
def ioRef : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | _, [] => []
  | fuel + 1, bs => (bs.take 16).reverse ++ ioRef fuel (bs.drop 16)

/-- A linear-congruential stream. -/
def ioLcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- The block sizes, which are edge sizes first, then every size from 1 to 33, then pseudo-random
sizes biased towards the edges. -/
def ioSizes : List Nat :=
  let edges := [1, 1, 1, 2, 15, 16, 17, 31, 32, 33, 1, 16, 16, 15, 1, 17, 48, 49]
  let ramp := (List.range 33).map (· + 1)
  let rec rnd (s : UInt64) : Nat → List Nat
    | 0 => []
    | n + 1 =>
      let s' := ioLcg s
      let v := (s' >>> 33).toNat
      let k := if v % 3 = 0 then [1, 15, 16, 17, 31, 32, 33][v / 3 % 7]! else v / 3 % 40 + 1
      k :: rnd s' n
  edges ++ ramp ++ rnd 7 (360 - edges.length - ramp.length)

/-- The byte stream, edge bytes such as `0` and `255` mixed with pseudo-random ones. -/
def ioBytes (n : Nat) : List UInt8 :=
  let rec go (s : UInt64) : Nat → List UInt8
    | 0 => []
    | n + 1 =>
      let s' := ioLcg s
      let v := (s' >>> 40).toNat
      (if v % 5 = 0 then [0, 255, 10, 1, 128][v / 5 % 5]! else (v / 5 % 256).toUInt8) :: go s' n
  go 3 n

/-- The blocks, cut out of `ioBytes` with the sizes `ioSizes`. -/
def ioBlocks : List (List UInt8) :=
  let sizes := ioSizes
  let bytes := ioBytes (sizes.foldl (· + ·) 0)
  let rec cut : List Nat → List UInt8 → List (List UInt8)
    | [], _ => []
    | k :: ks, bs => bs.take k :: cut ks (bs.drop k)
  cut sizes bytes

def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])

/-- The script of the driver, with one pair of lines per block, `I <hex>` for the bytes to write and
`O <hex>` for the bytes to expect. -/
def ioScript : String :=
  String.join (ioBlocks.map fun b => s!"I {hexOf b}\nO {hexOf (ioRef (b.length + 1) b)}\n")

-- the reference reads a block of 18 as 16 and 2
#guard ioRef 5 ((List.range 18).map (·.toUInt8)) =
  ((List.range 16).reverse.map (·.toUInt8)) ++ [17, 16]
#guard ioBlocks.length = 360
#guard ioBlocks.all (fun b => !b.isEmpty)

end Millipede.Tests.Differential
