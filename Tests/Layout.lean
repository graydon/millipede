import Millipede.Core.Data

/-!
# Tests for data layout

A value's layout follows the C rules for naturally aligned fields. This suite builds a dozen
structs and sums with `Data.struct` and `Data.sum`, which `deriving Data` also produces, and
compares their sizes, alignments and field offsets with C. The comparison is made statically by
`decide` against values recorded from gcc, and again at each run of `scripts/layout-check.sh`,
which compiles the same structs in `scripts/layout-check.c` and diffs their layout with
`report`. `scripts/layout-check.sh --selftest` shows that the check catches seeded bugs, a
packed C struct and a Lean layout without tail padding or without field alignment.

The suite also checks `encode` and `repr` on concrete values.
-/

namespace Millipede.Tests.Layout

open Millipede

/-- `struct S1 { uint8_t a; uint64_t b; }` -/
structure S1 where
  a : UInt8
  b : UInt64
instance : Data S1 := Data.struct [⟨S1.a⟩, ⟨S1.b⟩]

/-- `struct S2 { uint8_t a; uint16_t b; uint8_t c; }` -/
structure S2 where
  a : UInt8
  b : UInt16
  c : UInt8
instance : Data S2 := Data.struct [⟨S2.a⟩, ⟨S2.b⟩, ⟨S2.c⟩]

/-- `struct S3 { uint32_t a; uint8_t b; }` (tail padding) -/
structure S3 where
  a : UInt32
  b : UInt8
instance : Data S3 := Data.struct [⟨S3.a⟩, ⟨S3.b⟩]

/-- `struct S4 { uint64_t a; uint8_t b[3]; uint16_t c; }` -/
structure S4 where
  a : UInt64
  b : Arr UInt8 3
  c : UInt16
instance : Data S4 := Data.struct [⟨S4.a⟩, ⟨S4.b⟩, ⟨S4.c⟩]

/-- `struct S5 { uint8_t a; struct S1 inner; uint8_t c; }` (nested struct) -/
structure S5 where
  a : UInt8
  inner : S1
  c : UInt8
instance : Data S5 := Data.struct [⟨S5.a⟩, ⟨S5.inner⟩, ⟨S5.c⟩]

/-- `struct S6 { bool flag; int32_t x; int16_t y; }` -/
structure S6 where
  flag : Bool
  x : Int32
  y : Int16
instance : Data S6 := Data.struct [⟨S6.flag⟩, ⟨S6.x⟩, ⟨S6.y⟩]

/-- `struct S7 { }` (GNU C: size 0) -/
structure S7 where
instance : Data S7 := Data.struct []

/-- `struct S8 { uint16_t a[5]; uint8_t b; }` -/
structure S8 where
  a : Arr UInt16 5
  b : UInt8
instance : Data S8 := Data.struct [⟨S8.a⟩, ⟨S8.b⟩]

/-- `struct S9 { int8_t a; int64_t b; int8_t c; }` -/
structure S9 where
  a : Int8
  b : Int64
  c : Int8
instance : Data S9 := Data.struct [⟨S9.a⟩, ⟨S9.b⟩, ⟨S9.c⟩]

/-- `struct S10 { uint8_t a; char g[0]; uint32_t b; }`, with a ghost field, the proof of an
invariant, between two real ones. The ghost field occupies no bytes. -/
structure S10 where
  a : UInt8
  inv : PLift (a.toNat < 200)
  b : UInt32
instance : Data S10 := Data.struct [⟨S10.a⟩, Field.ghost S10, ⟨S10.b⟩]

/-- `struct S11 { uint8_t n; uint64_t cells[4]; }`, since the cells of `Slots` have no tags. -/
structure S11 where
  n : UInt8
  cells : Slots UInt64 4
instance : Data S11 := Data.struct [⟨S11.n⟩, ⟨S11.cells⟩]

/-- `struct S12 { struct { uint8_t x; uint16_t y; } p; uint8_t c; }` (a pair inside a struct) -/
structure S12 where
  p : UInt8 × UInt16
  c : UInt8
instance : Data S12 := Data.struct [⟨S12.p⟩, ⟨S12.c⟩]

/-- `struct S13 { uint32_t a[3]; uint64_t b; }` -/
structure S13 where
  a : Arr UInt32 3
  b : UInt64
instance : Data S13 := Data.struct [⟨S13.a⟩, ⟨S13.b⟩]

/-- An enum with payloads, `struct E1 { uint8_t tag; union { uint8_t a; uint64_t b;
struct { uint16_t x; uint32_t y; } c; } u; }`. -/
inductive E1 where
  | a (x : UInt8)
  | b (x : UInt64)
  | c (x : UInt16 × UInt32)
instance : Data E1 :=
  Data.sum [⟨fun | .a x => some x | _ => none⟩, ⟨fun | .b x => some x | _ => none⟩,
    ⟨fun | .c x => some x | _ => none⟩] (fun e => by cases e <;> simp)

/-- The offsets in a layout line, which are the field offsets of a struct or the tag and payload
offsets of a sum. -/
def offsets : Shape → List Nat
  | .prod fs => Shape.prodOffsets 0 fs
  | .sum vs => [0, Shape.payloadOffset vs]
  | _ => []

/-- The size, alignment and offsets of a shape. -/
def layout (s : Shape) : Nat × Nat × List Nat := (s.size, s.align, offsets s)

/-- The tested types, in the order of `scripts/layout-check.c`. -/
def table : List (String × Shape) :=
  [("S1", Data.shape S1), ("S2", Data.shape S2), ("S3", Data.shape S3),
   ("S4", Data.shape S4), ("S5", Data.shape S5), ("S6", Data.shape S6),
   ("S7", Data.shape S7), ("S8", Data.shape S8), ("S9", Data.shape S9),
   ("S10", Data.shape S10), ("S11", Data.shape S11), ("S12", Data.shape S12),
   ("S13", Data.shape S13), ("E1", Data.shape E1),
   ("ExceptU8U64", Data.shape (Except UInt8 UInt64)),
   ("OptionU32", Data.shape (Option UInt32))]

/-- The values recorded from gcc on `scripts/layout-check.c`, on which aarch64 and x86-64
agree. -/
def expected : List (Nat × Nat × List Nat) :=
  [(16, 8, [0, 8]), (6, 2, [0, 2, 4]), (8, 4, [0, 4]), (16, 8, [0, 8, 12]),
   (32, 8, [0, 8, 24]), (12, 4, [0, 4, 8]), (0, 1, []), (12, 2, [0, 10]),
   (24, 8, [0, 8, 16]), (8, 4, [0, 1, 4]), (40, 8, [0, 8]), (6, 2, [0, 4]),
   (24, 8, [0, 16]), (16, 8, [0, 8]), (16, 8, [0, 8]), (8, 4, [0, 4])]

theorem table_matches_gcc : table.map (fun p => layout p.2) = expected := by decide

/-- The report that `scripts/layout-check.sh` diffs against C, one line per type with its name,
size, alignment and offsets. -/
def report (lay : Shape → Nat × Nat × List Nat := layout) : String :=
  String.join <| table.map fun (n, s) =>
    let (sz, al, os) := lay s
    s!"{n} {sz} {al}" ++ String.join (os.map (s!" {·}")) ++ "\n"

/-! ## Offsets agree with the general lemmas -/

example : Shape.fieldOffset (Fields.shapes [⟨S4.a⟩, ⟨S4.b⟩, ⟨S4.c⟩]) 2 = 12 := by decide
example : (Data.shape (Arr S2 4)).size = 24 := by decide
example : (Data.shape S2).elemOffset 3 = 18 := by decide

/-! ## `encode` / `repr` on values -/

/-- `encode` zero-fills padding and lays fields out little-endian at their offsets. -/
example : Data.encodeBytes (S1.mk 0xAB 0x0102030405060708) =
    [0xAB, 0, 0, 0, 0, 0, 0, 0, 8, 7, 6, 5, 4, 3, 2, 1] := by decide
example : Data.encodeBytes (S2.mk 1 0x0302 4) = [1, 0, 2, 3, 4, 0] := by decide
example : Data.encodeBytes (E1.c (0x0201, 0x06050403)) =
    [2, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 4, 5, 6] := by decide
example : Data.encodeBytes (Except.ok (ε := UInt8) (7 : UInt64)) =
    [1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0] := by decide
example : Data.encodeBytes (some (5 : UInt32)) = [1, 0, 0, 0, 5, 0, 0, 0] := by decide
example : Data.encodeBytes (#v[(1 : UInt16), 2] : Arr UInt16 2) = [1, 0, 2, 0] := by decide
example : Data.encodeBytes (α := Slots UInt8 2) #v[none, some 9] = [0, 9] := by decide
/-- The same vector as `Arr (Option U8) 2` has tags. -/
example : Data.encodeBytes (α := Arr (Option UInt8) 2) #v[none, some 9] = [0, 0, 1, 9] := by
  decide

/-- Padding is arbitrary: garbage in the padding of `S1` still represents the value. -/
example : Data.reprBytes (S1.mk 0xAB 1) [0xAB, 9, 9, 9, 9, 9, 9, 9, 1, 0, 0, 0, 0, 0, 0, 0] :=
  ⟨rfl, by
    refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩⟩

/-- The bytes of an empty cell of `Slots` are arbitrary. -/
example : Data.repr (α := Slots UInt8 2) #v[none, some 9] ⟨[0x55, 9], rfl⟩ := by
  intro i hi
  match i, hi with
  | 0, _ => trivial
  | 1, _ => exact ⟨rfl, rfl⟩

/-- The bytes of a field are not arbitrary, so a wrong byte in field `b` is rejected. -/
example : ¬ Data.reprBytes (S1.mk 0xAB 1) [0xAB, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0] := by
  intro ⟨_, _, ⟨_, hb⟩, _⟩
  have : slice [0xAB, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0] 8 8 = natBytes 8 1 := hb
  exact absurd this (by decide)

/-- A derived struct is determinate, since its fields determine the value. -/
instance : Data.Determinate S1 :=
  Data.struct_determinate _
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> infer_instance)
    (fun s t h => by
      cases s; cases t
      have ha := h ⟨S1.a⟩ (by simp); have hb := h ⟨S1.b⟩ (by simp)
      simp_all)

end Millipede.Tests.Layout
