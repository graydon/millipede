import Millipede.Target.SelMem
import Millipede.Object.LinkProof

/-!
# The loader's start

This module derives, from the initial state of a linked image, the facts that every ISA's start
state `Init` needs. It holds for any page size `2^pb` with `pb ≥ 3` and any stack top `T ≤ 2^47`
of the link configuration, which are the ABI's.

No segment of a valid image reaches its limit or beyond. So the stack region, the
`2^(pb-3) · stackPages cfg` words from the linker's limit up to `T`, is readable, writable and
zero, its top address is `T`, and it holds the configured stack size (`link_stack`). For any
assembler with laws, `link_start` adds that the program is loaded in W^X memory under the
linker's resolution, the entry function is at the image's entry, the zero-initialised regions
are in place below the stack region, and the region's base is page-aligned. Each ISA adds its
entry registers and its own alignment facts.
-/

namespace Millipede.Sel

/-! ## The segments of a valid image end below its limit -/

/-- No segment of a valid image touches a page at or above `L`. -/
theorem segPerm_none {pb L : Nat} : ∀ (sgs : List Segment) (pg : Nat),
    (∀ sg ∈ sgs, Image.segOk pb L sg = true) → L ≤ pg * 2 ^ pb → Image.segPerm pb sgs pg = none
  | [], _, _, _ => rfl
  | sg :: sgs, pg, h, hL => by
    have h1 := h sg List.mem_cons_self
    simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq] at h1
    have hc : sg.coversPage pb pg = false := by
      simp only [Segment.coversPage, Segment.lastPage, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      right
      have : (sg.vaddr.toNat + sg.memSize - 1) / 2 ^ pb < pg :=
        (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos pb)).mpr (by omega)
      exact decide_eq_false (by omega)
    simp only [Image.segPerm, hc, Bool.false_eq_true, ite_false]
    exact segPerm_none sgs pg (fun s hs => h s (List.mem_cons_of_mem _ hs)) hL

/-- A valid image has no byte at or above `L`. -/
theorem segByte_zero {pb L : Nat} : ∀ (sgs : List Segment) (a : UInt64),
    (∀ sg ∈ sgs, Image.segOk pb L sg = true) → L ≤ a.toNat → Image.segByte sgs a = 0
  | [], _, _, _ => rfl
  | sg :: sgs, a, h, hL => by
    have h1 := h sg List.mem_cons_self
    simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq] at h1
    have hc : sg.contains a = false := by
      simp only [Segment.contains, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right; omega
    simp only [Image.segByte, hc, Bool.false_eq_true, ite_false]
    exact segByte_zero sgs a (fun s hs => h s (List.mem_cons_of_mem _ hs)) hL

/-- Bytes from `c` on, all at or above a valid image's limit, are zero. -/
theorem bytesFrom_zero {pb L : Nat} {m : Memory} {sgs : List Segment}
    (hm : ∀ a, m.bytes a = Image.segByte sgs a) (hseg : ∀ sg ∈ sgs, Image.segOk pb L sg = true) :
    ∀ (n c : Nat), L ≤ c → c + n ≤ 2 ^ 64 → bytesFrom m (UInt64.ofNat c) n = List.replicate n 0
  | 0, _, _, _ => rfl
  | n + 1, c, h1, h2 => by
    simp only [bytesFrom, List.replicate_succ]
    congr 1
    · rw [hm]; exact segByte_zero _ _ hseg (by rw [toNat_ofNat_lt (by omega)]; omega)
    · rw [show UInt64.ofNat c + 1 = UInt64.ofNat (c + 1) by rw [UInt64.ofNat_add]; rfl]
      exact bytesFrom_zero hm hseg n (c + 1) (by omega) (by omega)

/-! ## The stack region of a linked image -/

/-- The number of words of the stack region of a link configuration, `2^(pb-3)` for each stack
page. -/
def stackWords (cfg : Link.Config) : Nat := 2 ^ (cfg.pageBits - 3) * Link.stackPages cfg

theorem link_stackSize {cfg : Link.Config} {objs : List Obj} {img : Image}
    (hk : Link.link cfg objs = .ok img) : img.stackSize = cfg.stackSize := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := (Link.link_ok hk).out
  rfl

/-- The `stackWords cfg` words of a linked image from the linker's limit are readable, writable
and zero, the address just above them is the stack top, and they hold the configured stack
size. -/
theorem link_stack {isa : Isa} (abi : Abi isa) {cfg : Link.Config} {objs : List Obj}
    {img : Image} (hk : Link.link cfg objs = .ok img) (hpb : abi.pageBits = cfg.pageBits)
    (hst : abi.stackTop = cfg.stackTop) (h3 : 3 ≤ cfg.pageBits)
    (h47 : cfg.stackTop.toNat ≤ 2 ^ 47) :
    Region (img.init abi).mem (Link.limit cfg) (stackWords cfg) ∧
      (∀ k, k < stackWords cfg → word (img.init abi).mem (Link.limit cfg) k = 0) ∧
      wa (Link.limit cfg) (stackWords cfg) = cfg.stackTop ∧
      cfg.stackSize ≤ 8 * stackWords cfg := by
  have hv := Link.link_valid abi hk hpb hst
  have hok := Link.link_ok hk
  have hn : img.stackPages cfg.pageBits = Link.stackPages cfg := by
    simp [Image.stackPages, Link.stackPages, link_stackSize hk]
  simp only [Image.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, hpb,
    hst, hn] at hv
  have hseg : ∀ sg ∈ img.segments, Image.segOk cfg.pageBits (Link.limit cfg) sg = true :=
    hv.1.2
  obtain ⟨-, hmod, hle⟩ := hok.stack
  -- the arithmetic, over `P = 2^pb`, `n` pages, `t = T / P`
  have h8 : 8 * stackWords cfg = 2 ^ cfg.pageBits * Link.stackPages cfg := by
    rw [stackWords, ← Nat.mul_assoc, show 8 = 2 ^ 3 from rfl, ← Nat.pow_add,
      Nat.add_sub_cancel' h3]
  have hT := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
  have hlim : Link.limit cfg + 8 * stackWords cfg = cfg.stackTop.toNat := by
    rw [h8, Link.limit, Nat.mul_comm (2 ^ _) (Link.stackPages cfg), ← Nat.add_mul,
      Nat.sub_add_cancel hle, hT]
  have hP := Nat.two_pow_pos cfg.pageBits
  have hsz : cfg.stackSize ≤ 8 * stackWords cfg := by
    rw [h8, Link.stackPages]
    have := Nat.div_add_mod (cfg.stackSize + 2 ^ cfg.pageBits - 1) (2 ^ cfg.pageBits)
    have := Nat.mod_lt (cfg.stackSize + 2 ^ cfg.pageBits - 1) hP
    omega
  have hbytes : ∀ a, (img.init abi).mem.bytes a = Image.segByte img.segments a := fun _ => rfl
  have hR : Region (img.init abi).mem (Link.limit cfg) (stackWords cfg) := by
    refine ⟨fun i hi => ?_, by omega⟩
    have ha : (UInt64.ofNat (Link.limit cfg + i)).toNat = Link.limit cfg + i :=
      toNat_ofNat_lt (by omega)
    have hlo : cfg.stackTop.toNat / 2 ^ cfg.pageBits - Link.stackPages cfg ≤
        (Link.limit cfg + i) / 2 ^ cfg.pageBits :=
      (Nat.le_div_iff_mul_le hP).mpr (by unfold Link.limit; omega)
    have hhi : (Link.limit cfg + i) / 2 ^ cfg.pageBits < cfg.stackTop.toNat / 2 ^ cfg.pageBits :=
      (Nat.div_lt_iff_lt_mul hP).mpr (by rw [hT]; omega)
    have hperm : (img.init abi).mem.permAt (UInt64.ofNat (Link.limit cfg + i)) = Perm.rw := by
      show img.pagePerm abi.pageBits abi.stackTop
        ((UInt64.ofNat (Link.limit cfg + i)).toNat / 2 ^ abi.pageBits) = Perm.rw
      rw [ha, hpb, hst]
      have hnone : Image.segPerm cfg.pageBits img.segments
          ((Link.limit cfg + i) / 2 ^ cfg.pageBits) = none :=
        segPerm_none _ _ hseg (by unfold Link.limit; exact Nat.mul_le_mul_right _ hlo)
      have hstk : img.isStackPage cfg.pageBits cfg.stackTop
          ((Link.limit cfg + i) / 2 ^ cfg.pageBits) = true := by
        simp only [Image.isStackPage, Bool.and_eq_true, decide_eq_true_eq, hn]
        exact ⟨hlo, hhi⟩
      simp only [Image.pagePerm, hnone, hstk, ite_true]
    simp only [Memory.readable, Memory.writable, hperm]
    exact ⟨rfl, rfl⟩
  refine ⟨hR, fun k hk => ?_, ?_, hsz⟩
  · unfold word wa
    rw [bytesFrom_zero hbytes hseg 8 _ (by omega) (by omega)]
    rfl
  · unfold wa
    rw [hlim, UInt64.ofNat_toNat]

/-! ## The start of a linked, assembled program -/

section Start
variable {A : Asm.Arch}

/-- What the loader provides every selection, where `σ` is the linker's resolution and the
stack region is `N` words from `lo`. -/
structure LinkStart (abi : Abi A.isa) (cfg : Link.Config) (img : Image) (AP : Asm.Prog A)
    (σ : String → Option UInt64) (lo N : Nat) : Prop where
  world : (img.init abi).world = World.init
  wx : (img.init abi).mem.WxorX
  loaded : AP.Loaded σ (img.init abi).mem
  entry : ∀ f ∈ AP.funs, f.name = cfg.entry → σ f.name = some img.entry
  region : Region (img.init abi).mem lo N
  zero : ∀ k, k < N → word (img.init abi).mem lo k = 0
  top : wa lo N = abi.stackTop
  size : cfg.stackSize ≤ 8 * N
  lo_page : lo % 2 ^ abi.pageBits = 0
  words : N = 2 ^ (abi.pageBits - 3) * Link.stackPages cfg
  bss : AP.BssAt σ (img.init abi).mem
  below : ∀ b ∈ AP.bss, ∀ D, σ b.1 = some D → D.toNat + b.2 ≤ lo

/-- Linking one object assembled by an assembler with laws gives a `LinkStart` at the linker's
resolution, its limit and `stackWords`, for a page size of at least 8 bytes and a stack top at
or below `2^47`. -/
theorem link_start {asm : Asm.Assembler A} (hl : asm.Laws) {AP : Asm.Prog A} {obj : Obj}
    (hA : Asm.assemble asm AP = .ok obj) {cfg : Link.Config} {img : Image}
    (hk : Link.link cfg [obj] = .ok img) (abi : Abi A.isa) (hpb : abi.pageBits = cfg.pageBits)
    (hst : abi.stackTop = cfg.stackTop) (h3 : 3 ≤ cfg.pageBits)
    (h47 : cfg.stackTop.toNat ≤ 2 ^ 47) :
    LinkStart abi cfg img AP (Link.resolve (Link.layout cfg [obj]) [obj] 0) (Link.limit cfg)
      (stackWords cfg) := by
  obtain ⟨hloaded, hwx, hentry⟩ := Asm.link_assemble hl hA hk abi hpb hst
  obtain ⟨hbss, hbelow⟩ := Asm.link_assemble_bss hA hk abi hpb hst
  obtain ⟨hR, hzero, htop, hsz⟩ := link_stack abi hk hpb hst h3 h47
  exact ⟨rfl, hwx, hloaded, hentry, hR, hzero, by rw [htop, hst], hsz,
    by rw [hpb]; exact Nat.mul_mod_left _ _, by rw [hpb]; rfl, hbss, hbelow⟩

end Start

end Millipede.Sel
