import Millipede.Object.Link
import Millipede.Compile.AssembleProof

/-!
# The linker's laws

This file proves what a successful link `h : link cfg objs = .ok img` guarantees, for any ISA and
any objects. `link_section` says that every section of every object has an address at which the
image holds the section's bytes with its relocations applied, followed by its zero fill, on pages
with the permissions of the section's kind. `link_init_byte` restates this for the initial machine
memory. `link_symbol` says that each symbol resolves to its section's address plus its offset,
`link_entry` that the entry point is the address of the global symbol `cfg.entry`, and
`link_valid` that the image is valid for an ABI with the linker's page size and stack top. Its
segments are page-aligned, non-empty, in address order on disjoint pages, below the stack, and
never both writable and executable, so the initial memory is W^X by `link_wxorx`.

The second part composes the linker with an assembler that satisfies `Asm.Assembler.Laws`, for
every architecture. `link_assemble` says that linking the object of `assemble asm P` gives an
initial state in which `P` is loaded, the memory is W^X, and the function named `cfg.entry` sits
at the entry address. `link_assemble_bss` says
that each zero-initialised region of `P` sits at its symbol, readable, writable and zero, and
ends at or below the linker's stack limit. The last section gives the x64 instances.
-/

namespace Millipede.Link

/-! ## Unpacking a successful link -/

/-- Everything that a successful `link` checked and computed. -/
structure Ok (cfg : Config) (objs : List Obj) (img : Image) : Prop where
  names : ∀ o ∈ objs, (o.symbols.map (·.name)).Nodup
  globals : (globalNames objs).Nodup
  symSec : ∀ o ∈ objs, ∀ s ∈ o.symbols, s.sec < o.sections.length
  base : cfg.base % 2 ^ cfg.pageBits = 0
  stack : 0 < cfg.stackSize ∧ cfg.stackTop.toNat % 2 ^ cfg.pageBits = 0 ∧
    stackPages cfg ≤ cfg.stackTop.toNat / 2 ^ cfg.pageBits
  fits : (layout cfg objs).rwEnd ≤ limit cfg
  out : ∃ T R W e,
    emit (content (layout cfg objs) objs) (layout cfg objs).textBase (groupItems .text objs) =
      some T ∧
    emit (content (layout cfg objs) objs) (layout cfg objs).roBase (groupItems .rodata objs) =
      some R ∧
    emit (content (layout cfg objs) objs) (layout cfg objs).rwBase (groupItems .rw objs) =
      some W ∧
    globalAddr (layout cfg objs) objs cfg.entry = some e ∧
    img = { segments := [mkSeg (layout cfg objs).textBase (fill cfg (layout cfg objs).textBase T) .rx,
              mkSeg (layout cfg objs).roBase (fill cfg (layout cfg objs).roBase R) .r_,
              mkSeg (layout cfg objs).rwBase (fill cfg (layout cfg objs).rwBase W) .rw
                true].filter
                (fun sg => 0 < sg.memSize)
            entry := e, stackSize := cfg.stackSize }

theorem req_ok {b : Bool} {m : String} {u : Unit} (h : req b m = .ok u) : b = true := by
  unfold req at h; split at h
  · assumption
  · cases h

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem link_ok {cfg : Config} {objs : List Obj} {img : Image} (h : link cfg objs = .ok img) :
    Ok cfg objs img := by
  unfold link at h
  obtain ⟨_, h1, h⟩ := bind_ok h
  obtain ⟨_, h2, h⟩ := bind_ok h
  obtain ⟨_, h3, h⟩ := bind_ok h
  obtain ⟨_, h4, h⟩ := bind_ok h
  obtain ⟨_, h5, h⟩ := bind_ok h
  obtain ⟨_, h6, h⟩ := bind_ok h
  obtain ⟨_, h7, h⟩ := bind_ok h
  have e1 := req_ok h1; have e2 := req_ok h2; have e3 := req_ok h3; have e5 := req_ok h5
  have e6 := req_ok h6; have e7 := req_ok h7
  simp only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at e1 e2 e3 e5 e6 e7
  dsimp only at h
  split at h
  · rename_i T R W hT hR hW
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨e1, e2, e3, e5, ⟨e6.1.1, e6.1.2, e6.2⟩, e7, T, R, W, e, hT, hR, hW, he, rfl⟩
  · cases h

/-! ## Arithmetic of the layout -/

theorem le_alignUp (a k : Nat) : a ≤ alignUp a k := by
  unfold alignUp
  split
  · exact Nat.le_refl a
  · rename_i hk
    have h1 := Nat.mod_add_div (a + k - 1) k
    have h2 := Nat.mod_lt (a + k - 1) (Nat.pos_of_ne_zero hk)
    rw [Nat.mul_comm] at h1
    omega

theorem alignUp_mod (a k : Nat) (hk : 0 < k) : alignUp a k % k = 0 := by
  unfold alignUp
  have : k ≠ 0 := by omega
  simp only [this, ↓reduceIte]
  exact Nat.mul_mod_left _ _

/-- Rounding up to a multiple of `k` stays at or below any multiple of `k` above. -/
theorem alignUp_le {a b k : Nat} (hk : 0 < k) (hb : b % k = 0) (h : a ≤ b) : alignUp a k ≤ b := by
  unfold alignUp
  have : k ≠ 0 := by omega
  simp only [this, ↓reduceIte]
  have h1 : (a + k - 1) / k < b / k + 1 := (Nat.div_lt_iff_lt_mul hk).2 (by
    have := Nat.div_add_mod b k
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega)
  have := Nat.div_add_mod b k
  have h2 : (a + k - 1) / k * k ≤ b / k * k := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_comm k (b / k)] at this
  omega

/-- Dropping trailing zeros keeps every byte, because `Segment.byteAt` reads 0 past the end. -/
theorem dropZeros_getD : ∀ (bs : List UInt8) (i : Nat), (dropZeros bs)[i]?.getD 0 = bs[i]?.getD 0
  | [], _ => rfl
  | b :: bs, i => by
    have ih := dropZeros_getD bs
    simp only [dropZeros]
    split
    · rename_i h
      rw [h] at ih
      cases i with
      | zero => split <;> simp [*]
      | succ k =>
        have := ih k
        split <;> simp only [List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none] at this ⊢ <;>
          exact this
    · cases i with
      | zero => rfl
      | succ k => simpa using ih k

theorem dropZeros_length_le : ∀ bs : List UInt8, (dropZeros bs).length ≤ bs.length
  | [] => Nat.le_refl _
  | b :: bs => by
    have := dropZeros_length_le bs
    simp only [dropZeros]; split
    · split <;> simp
    · simpa using this

@[simp] theorem getD_trim (t : Bool) (bs : List UInt8) (i : Nat) :
    (if t then dropZeros bs else bs).getD i 0 = bs.getD i 0 := by
  cases t <;> simp [List.getD_eq_getElem?_getD, dropZeros_getD]

theorem trim_length_le (t : Bool) (bs : List UInt8) :
    (if t then dropZeros bs else bs).length ≤ bs.length := by
  cases t <;> simp [dropZeros_length_le]

theorem fill_prefix (cfg : Config) (base : Nat) (bs : List UInt8) :
    ∃ t, fill cfg base bs = bs ++ t := by
  unfold fill; split
  · exact ⟨_, rfl⟩
  · exact ⟨[], by simp⟩

/-- A group's filled bytes still end at or below any page boundary its bytes end below. -/
theorem fill_end {cfg : Config} {base b : Nat} {bs : List UInt8}
    (hb : b % 2 ^ cfg.pageBits = 0) (h : base + bs.length ≤ b) :
    bs.length ≤ (fill cfg base bs).length ∧ base + (fill cfg base bs).length ≤ b := by
  unfold fill; split
  · have := alignUp_le (Nat.two_pow_pos cfg.pageBits) hb h
    have := le_alignUp (base + bs.length) (2 ^ cfg.pageBits)
    simp only [List.length_append, List.length_replicate]; omega
  · omega

theorem le_placeEnd : ∀ (cur : Nat) (its : List Item), cur ≤ placeEnd cur its
  | _, [] => Nat.le_refl _
  | cur, it :: its => by
    have := le_alignUp cur it.sec.align
    have := le_placeEnd (alignUp cur it.sec.align + it.sec.size) its
    simp only [placeEnd]; omega

/-- A placed section lies after `cur` and ends by `placeEnd`. -/
theorem place_mem : ∀ (cur : Nat) (its : List Item) (p : Item × Nat), p ∈ place cur its →
    p.1 ∈ its ∧ cur ≤ p.2 ∧ p.2 + p.1.sec.size ≤ placeEnd cur its
  | _, [], _, h => by simp [place] at h
  | cur, it :: its, p, h => by
    simp only [place, List.mem_cons] at h
    have h1 := le_alignUp cur it.sec.align
    have h2 := le_placeEnd (alignUp cur it.sec.align + it.sec.size) its
    rcases h with rfl | h
    · exact ⟨List.mem_cons_self, h1, h2⟩
    · obtain ⟨a, b, c⟩ := place_mem _ its p h
      exact ⟨List.mem_cons_of_mem _ a, by omega, c⟩

/-- Every section is placed. -/
theorem mem_place : ∀ (cur : Nat) (its : List Item) (it : Item), it ∈ its →
    ∃ a, (it, a) ∈ place cur its
  | _, [], _, h => by simp at h
  | cur, it' :: its, it, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, List.mem_cons_self⟩
    · obtain ⟨a, ha⟩ := mem_place _ its it h
      exact ⟨a, List.mem_cons_of_mem _ ha⟩

/-- Every placed section's contents sit at its address in the bytes of its group. -/
theorem emit_spec (cont : Item → Nat → Option (List UInt8))
    (hc : ∀ it a X, cont it a = some X → X.length = it.sec.size) :
    ∀ (cur : Nat) (its : List Item) (B : List UInt8), emit cont cur its = some B →
      cur + B.length = placeEnd cur its ∧
      ∀ p ∈ place cur its, ∃ X, cont p.1 p.2 = some X ∧
        ∀ k, k < X.length → B[p.2 - cur + k]? = X[k]?
  | _, [], B, h => by cases h; exact ⟨rfl, fun _ h => by simp [place] at h⟩
  | cur, it :: its, B, h => by
    simp only [emit] at h
    split at h
    · rename_i X B' hX hB'
      cases h
      have hal := le_alignUp cur it.sec.align
      have hXl := hc _ _ _ hX
      obtain ⟨ih1, ih2⟩ := emit_spec cont hc _ its B' hB'
      refine ⟨?_, ?_⟩
      · simp only [placeEnd, List.length_append, List.length_replicate]; omega
      · intro p hp
        simp only [place, List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨X, hX, fun k hk => ?_⟩
          rw [List.append_assoc, List.getElem?_append_right (by simp),
            List.getElem?_append_left (by simp; omega)]
          simp
        · obtain ⟨Y, hY, hk⟩ := ih2 p hp
          have := (place_mem _ its p hp).2.1
          refine ⟨Y, hY, fun k hkl => ?_⟩
          rw [List.getElem?_append_right (by simp; omega)]
          rw [← hk k hkl]
          congr 1
          simp; omega
    · cases h

/-! ## Sections and their keys -/

theorem mem_secItems : ∀ (j : Nat) (rs : List Reloc) (i : Nat) (ss : List Section) (it : Item),
    it ∈ secItems j rs i ss → it.obj = j ∧ it.relocs = rs ∧ i ≤ it.idx ∧ ss[it.idx - i]? = some it.sec
  | _, _, _, [], _, h => by simp [secItems] at h
  | j, rs, i, s :: ss, it, h => by
    simp only [secItems, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨a, b, c, d⟩ := mem_secItems j rs (i + 1) ss it h
      refine ⟨a, b, by omega, ?_⟩
      have : it.idx - i = (it.idx - (i + 1)) + 1 := by omega
      rw [this]; simpa using d

/-- An item's key `(obj, idx)` names its section and its object's relocations. -/
theorem mem_items : ∀ (j : Nat) (objs : List Obj) (it : Item), it ∈ items j objs →
    j ≤ it.obj ∧ ∃ o, objs[it.obj - j]? = some o ∧ o.sections[it.idx]? = some it.sec ∧
      it.relocs = o.relocs
  | _, [], _, h => by simp [items] at h
  | j, o :: os, it, h => by
    simp only [items, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨a, b, _, d⟩ := mem_secItems j o.relocs 0 o.sections it h
      refine ⟨by omega, o, by simp [a], by simpa using d, b⟩
    · obtain ⟨a, o', b, c, d⟩ := mem_items (j + 1) os it h
      refine ⟨by omega, o', ?_, c, d⟩
      have : it.obj - j = (it.obj - (j + 1)) + 1 := by omega
      rw [this]; simpa using b

theorem secItems_mem : ∀ (j : Nat) (rs : List Reloc) (i : Nat) (ss : List Section) (k : Nat)
    (s : Section), ss[k]? = some s → ⟨j, i + k, s, rs⟩ ∈ secItems j rs i ss
  | _, _, _, [], _, _, h => by simp at h
  | j, rs, i, s' :: ss, k, s, h => by
    cases k with
    | zero => simp at h; subst h; simp [secItems]
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      have := secItems_mem j rs (i + 1) ss k s h
      simp only [secItems, List.mem_cons]
      right; rw [show i + (k + 1) = i + 1 + k by omega]; exact this

theorem items_mem : ∀ (j : Nat) (objs : List Obj) (k : Nat) (o : Obj) (i : Nat) (s : Section),
    objs[k]? = some o → o.sections[i]? = some s → ⟨j + k, i, s, o.relocs⟩ ∈ items j objs
  | _, [], _, _, _, _, h, _ => by simp at h
  | j, o' :: os, k, o, i, s, h, hs => by
    simp only [items, List.mem_append]
    cases k with
    | zero =>
      simp at h; subst h; left
      have := secItems_mem j o'.relocs 0 o'.sections i s hs
      simpa using this
    | succ k =>
      right
      have := items_mem (j + 1) os k o i s (by simpa using h) hs
      rwa [show j + (k + 1) = j + 1 + k by omega]

theorem item_eq {it : Item} {j i : Nat} {o : Obj} {s : Section} (hm : it ∈ items 0 objs)
    (hj : it.obj = j) (hi : it.idx = i) (ho : objs[j]? = some o) (hs : o.sections[i]? = some s) :
    it = ⟨j, i, s, o.relocs⟩ := by
  obtain ⟨_, o', h1, h2, h3⟩ := mem_items 0 objs it hm
  rw [Nat.sub_zero, hj, ho] at h1; cases h1
  rw [hi, hs] at h2; cases h2
  cases it; simp_all

theorem placed_mem {cfg : Config} {objs : List Obj} {p : Item × Nat}
    (h : p ∈ (layout cfg objs).placed) : p.1 ∈ items 0 objs := by
  simp only [layout, List.mem_append] at h
  rcases h with (h | h) | h <;>
    exact (List.mem_filter.1 (place_mem _ _ _ h).1).1

theorem mem_placed {cfg : Config} {objs : List Obj} {it : Item} (h : it ∈ items 0 objs) :
    ∃ a, (it, a) ∈ (layout cfg objs).placed := by
  simp only [layout, List.mem_append]
  have hg : ∀ g, it.sec.kind.group = g → it ∈ groupItems g objs := fun g hg =>
    List.mem_filter.2 ⟨h, by simp [hg]⟩
  cases hk : it.sec.kind.group with
  | text => obtain ⟨a, ha⟩ := mem_place _ _ _ (hg _ hk); exact ⟨a, .inl (.inl ha)⟩
  | rodata => obtain ⟨a, ha⟩ := mem_place _ _ _ (hg _ hk); exact ⟨a, .inl (.inr ha)⟩
  | rw => obtain ⟨a, ha⟩ := mem_place _ _ _ (hg _ hk); exact ⟨a, .inr ha⟩

/-- Every section of every object has an address, and its placement is recorded. -/
theorem secAddr_spec {cfg : Config} {objs : List Obj} {j i : Nat} {o : Obj} {s : Section}
    (ho : objs[j]? = some o) (hs : o.sections[i]? = some s) :
    ∃ A, secAddr (layout cfg objs) j i = some A ∧
      ((⟨j, i, s, o.relocs⟩ : Item), A) ∈ (layout cfg objs).placed := by
  have hm : (⟨j, i, s, o.relocs⟩ : Item) ∈ items 0 objs := by
    simpa using items_mem 0 objs j o i s ho hs
  obtain ⟨a, ha⟩ := mem_placed (cfg := cfg) hm
  unfold secAddr
  cases hf : (layout cfg objs).placed.find? (fun p => p.1.obj == j && p.1.idx == i) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ ha)
  | some p =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    have := item_eq (placed_mem h2) h1.1 h1.2 ho hs
    obtain ⟨it, A⟩ := p
    simp only at this; subst this
    exact ⟨A, rfl, h2⟩

/-! ## Memory of an image whose segments are in address order -/

/-- Segments in increasing address order, each ending before the next starts. -/
def Chain (segs : List Segment) : Prop :=
  segs.Pairwise (fun s t => s.vaddr.toNat + s.memSize ≤ t.vaddr.toNat)

theorem segByte_of_mem : ∀ {segs : List Segment} {sg : Segment} {a : UInt64}, Chain segs →
    sg ∈ segs → sg.vaddr.toNat ≤ a.toNat → a.toNat < sg.vaddr.toNat + sg.memSize →
    Image.segByte segs a = sg.byteAt a
  | [], _, _, _, h, _, _ => by simp at h
  | t :: segs, sg, a, hc, hm, h1, h2 => by
    simp only [Chain, List.pairwise_cons] at hc
    simp only [Image.segByte]
    rcases List.mem_cons.1 hm with rfl | hm
    · simp [Segment.contains, h1, h2]
    · have := hc.1 sg hm
      have hn : t.contains a = false := by simp [Segment.contains]; omega
      rw [hn]; exact segByte_of_mem hc.2 hm h1 h2

theorem segPerm_of_mem {pb : Nat} : ∀ {segs : List Segment} {sg : Segment} {a : Nat}, Chain segs →
    (∀ t ∈ segs, t.vaddr.toNat % 2 ^ pb = 0) →
    sg ∈ segs → sg.vaddr.toNat ≤ a → a < sg.vaddr.toNat + sg.memSize →
    Image.segPerm pb segs (a / 2 ^ pb) = some sg.perm
  | [], _, _, _, _, h, _, _ => by simp at h
  | t :: segs, sg, a, hc, hal, hm, h1, h2 => by
    simp only [Chain, List.pairwise_cons] at hc
    have hP : 0 < 2 ^ pb := Nat.two_pow_pos pb
    simp only [Image.segPerm]
    rcases List.mem_cons.1 hm with rfl | hm
    · have f1 := Nat.div_le_div_right (c := 2 ^ pb) h1
      have f2 := Nat.div_le_div_right (c := 2 ^ pb)
        (show a ≤ sg.vaddr.toNat + sg.memSize - 1 by omega)
      have : sg.coversPage pb (a / 2 ^ pb) = true := by
        simp only [Segment.coversPage, Segment.firstPage, Segment.lastPage]
        simp [f1, f2]; omega
      simp [this]
    · have hle := hc.1 sg hm
      have hsa := hal sg (List.mem_cons_of_mem _ hm)
      have : t.coversPage pb (a / 2 ^ pb) = false := by
        apply Bool.eq_false_iff.2
        intro hcov
        simp only [Segment.coversPage, Segment.firstPage, Segment.lastPage, Bool.and_eq_true,
          decide_eq_true_eq] at hcov
        have hq1 := of_decide_eq_true hcov.2
        have hq0 := hcov.1.1
        have hc' : sg.vaddr.toNat = sg.vaddr.toNat / 2 ^ pb * 2 ^ pb :=
          (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hsa)).symm
        have hlt : (t.vaddr.toNat + t.memSize - 1) / 2 ^ pb < sg.vaddr.toNat / 2 ^ pb :=
          (Nat.div_lt_iff_lt_mul hP).2 (by omega)
        have := Nat.div_le_div_right (c := 2 ^ pb) h1
        omega
      rw [this]
      exact segPerm_of_mem hc.2 (fun u hu => hal u (List.mem_cons_of_mem _ hu)) hm h1 h2

/-- A chain of segments with page-aligned starts, each non-empty, is `sortedDisjoint`. -/
theorem sortedDisjoint_of_chain {pb : Nat} : ∀ {segs : List Segment}, Chain segs →
    (∀ t ∈ segs, t.vaddr.toNat % 2 ^ pb = 0 ∧ 0 < t.memSize) →
    Image.sortedDisjoint pb segs = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: rest, hc, hal => by
    have hc' := List.pairwise_cons.1 hc
    have hP : 0 < 2 ^ pb := Nat.two_pow_pos pb
    simp only [Image.sortedDisjoint, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, sortedDisjoint_of_chain hc'.2 (fun u hu => hal u (List.mem_cons_of_mem _ hu))⟩
    have hab := hc'.1 b List.mem_cons_self
    have ha := hal a List.mem_cons_self
    have hb := hal b (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [Segment.lastPage, Segment.firstPage]
    have hc2 : b.vaddr.toNat = b.vaddr.toNat / 2 ^ pb * 2 ^ pb :=
      (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb.1)).symm
    exact (Nat.div_lt_iff_lt_mul hP).2 (by omega)

/-! ## Facts about the layout -/

theorem limit_le (cfg : Config) : limit cfg ≤ cfg.stackTop.toNat := by
  unfold limit
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.div_mul_le_self _ _)

theorem layout_order (cfg : Config) (objs : List Obj) :
    let L := layout cfg objs
    L.textBase ≤ L.textEnd ∧ L.textEnd ≤ L.roBase ∧ L.roBase ≤ L.roEnd ∧ L.roEnd ≤ L.rwBase ∧
      L.rwBase ≤ L.rwEnd :=
  ⟨le_placeEnd _ _, le_alignUp _ _, le_placeEnd _ _, le_alignUp _ _, le_placeEnd _ _⟩

theorem content_length {L : Layout} {objs : List Obj} {it : Item} {a : Nat} {X : List UInt8}
    (h : content L objs it a = some X) : X.length = it.sec.size := by
  simp only [content, Option.map_eq_some_iff] at h
  obtain ⟨Y, hY, rfl⟩ := h
  simp [applyRelocs_length _ _ _ _ _ _ hY, Section.size]

/-- One group's segment holds the bytes of a section placed in it, with its permissions. -/
theorem group_mem {pb : Nat} {L : Layout} {objs : List Obj} {g : Group} {gb : Nat}
    {B B' : List UInt8} {segs : List Segment} {it : Item} {A : Nat}
    (hE : emit (content L objs) gb (groupItems g objs) = some B)
    (hp : (it, A) ∈ place gb (groupItems g objs)) (hB : ∃ t, B' = B ++ t)
    {tr : Bool} (hseg : 0 < B.length → mkSeg gb B' g.perm tr ∈ segs) (hc : Chain segs)
    (hal : ∀ t ∈ segs, t.vaddr.toNat % 2 ^ pb = 0) (hlim : gb + B'.length < 2 ^ 64) :
    ∃ Y, content L objs it A = some Y ∧ ∀ k, k < it.sec.size →
      Y[k]? = some (Image.segByte segs (UInt64.ofNat (A + k))) ∧
      Image.segPerm pb segs ((A + k) / 2 ^ pb) = some it.sec.kind.perm := by
  obtain ⟨t, rfl⟩ := hB
  simp only [List.length_append] at hlim
  obtain ⟨hlen, hsp⟩ := emit_spec _ (fun _ _ _ h => content_length h) gb _ B hE
  obtain ⟨Y, hY, hk⟩ := hsp _ hp
  obtain ⟨hm, h1, h2⟩ := place_mem _ _ _ hp
  dsimp only at h1 h2 hY
  have hg : it.sec.kind.group = g := by simpa using (List.mem_filter.1 hm).2
  have hYl := content_length hY
  refine ⟨Y, hY, fun k hkl => ?_⟩
  have hsm := hseg (by omega)
  have hgb : (UInt64.ofNat gb).toNat = gb := by simp [UInt64.toNat_ofNat']; omega
  have hak : (UInt64.ofNat (A + k)).toNat = A + k := by simp [UInt64.toNat_ofNat']; omega
  refine ⟨?_, ?_⟩
  · rw [segByte_of_mem hc hsm (by simp only [mkSeg]; rw [hgb, hak]; omega)
      (by simp only [mkSeg, List.length_append]; rw [hgb, hak]; omega)]
    simp only [Segment.byteAt, mkSeg, hgb, hak, getD_trim]
    have := hk k (by omega)
    rw [show A + k - gb = A - gb + k by omega, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega), this]
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  · have := segPerm_of_mem (pb := pb) hc hal hsm (a := A + k) (by simp [mkSeg, hgb]; omega)
      (by simp [mkSeg, hgb]; omega)
    rw [this]; simp [mkSeg, ← hg, group_perm]

/-! ## The image's segments -/

/-- The three candidate segments of a link, before empty ones are dropped. -/
def segs3 (cfg : Config) (L : Layout) (T R W : List UInt8) : List Segment :=
  [mkSeg L.textBase (fill cfg L.textBase T) .rx, mkSeg L.roBase (fill cfg L.roBase R) .r_,
    mkSeg L.rwBase (fill cfg L.rwBase W) .rw true]

/-- The image's segments are in address order, page-aligned and below the stack. -/
theorem segs_facts {cfg : Config} {objs : List Obj} {img : Image} (hok : Ok cfg objs img)
    {T R W : List UInt8}
    (hT : emit (content (layout cfg objs) objs) (layout cfg objs).textBase (groupItems .text objs) =
      some T)
    (hR : emit (content (layout cfg objs) objs) (layout cfg objs).roBase
      (groupItems .rodata objs) = some R)
    (hW : emit (content (layout cfg objs) objs) (layout cfg objs).rwBase (groupItems .rw objs) =
      some W) :
    Chain (segs3 cfg (layout cfg objs) T R W) ∧
    (∀ t ∈ segs3 cfg (layout cfg objs) T R W, t.vaddr.toNat % 2 ^ cfg.pageBits = 0 ∧
      t.vaddr.toNat + t.memSize ≤ limit cfg ∧ t.bytes.length ≤ t.memSize ∧
      ¬ (t.perm.w = true ∧ t.perm.x = true)) ∧
    (layout cfg objs).textBase + (fill cfg (layout cfg objs).textBase T).length < 2 ^ 64 ∧
    (layout cfg objs).roBase + (fill cfg (layout cfg objs).roBase R).length < 2 ^ 64 ∧
    (layout cfg objs).rwBase + (fill cfg (layout cfg objs).rwBase W).length < 2 ^ 64 := by
  have hc := fun it a X (h : content (layout cfg objs) objs it a = some X) => content_length h
  have eT := (emit_spec _ hc _ _ _ hT).1
  have eR := (emit_spec _ hc _ _ _ hR).1
  have eW := (emit_spec _ hc _ _ _ hW).1
  have ho := layout_order cfg objs
  have hfit := hok.fits
  have hl := limit_le cfg
  have h64 := cfg.stackTop.toNat_lt
  have hP : 0 < 2 ^ cfg.pageBits := Nat.two_pow_pos _
  have r1 : (layout cfg objs).textBase = cfg.base := rfl
  have r2 : (layout cfg objs).roBase = alignUp (layout cfg objs).textEnd (2 ^ cfg.pageBits) := rfl
  have r3 : (layout cfg objs).rwBase = alignUp (layout cfg objs).roEnd (2 ^ cfg.pageBits) := rfl
  have r4 : placeEnd (layout cfg objs).textBase (groupItems .text objs) =
    (layout cfg objs).textEnd := rfl
  have r5 : placeEnd (layout cfg objs).roBase (groupItems .rodata objs) =
    (layout cfg objs).roEnd := rfl
  have r6 : placeEnd (layout cfg objs).rwBase (groupItems .rw objs) =
    (layout cfg objs).rwEnd := rfl
  rw [r4] at eT; rw [r5] at eR; rw [r6] at eW
  obtain ⟨o1, o2, o3, o4, o5⟩ := ho
  have hlm : limit cfg % 2 ^ cfg.pageBits = 0 := Nat.mul_mod_left _ _
  have f1 := fill_end (cfg := cfg) (bs := T) (base := (layout cfg objs).textBase)
    (r2 ▸ alignUp_mod _ _ hP) (by rw [r2]; have := le_alignUp (layout cfg objs).textEnd (2 ^ cfg.pageBits); omega)
  have f2 := fill_end (cfg := cfg) (bs := R) (base := (layout cfg objs).roBase)
    (r3 ▸ alignUp_mod _ _ hP) (by rw [r3]; have := le_alignUp (layout cfg objs).roEnd (2 ^ cfg.pageBits); omega)
  have f3 := fill_end (cfg := cfg) (bs := W) (base := (layout cfg objs).rwBase) hlm (by omega)
  have n1 : (UInt64.ofNat (layout cfg objs).textBase).toNat = (layout cfg objs).textBase := by
    simp [UInt64.toNat_ofNat']; omega
  have n2 : (UInt64.ofNat (layout cfg objs).roBase).toNat = (layout cfg objs).roBase := by
    simp [UInt64.toNat_ofNat']; omega
  have n3 : (UInt64.ofNat (layout cfg objs).rwBase).toNat = (layout cfg objs).rwBase := by
    simp [UInt64.toNat_ofNat']; omega
  refine ⟨?_, ?_, by omega, by omega, by omega⟩
  · simp only [Chain, segs3, mkSeg, List.pairwise_cons, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, List.Pairwise.nil]
    rw [n1, n2, n3]
    refine ⟨⟨?_, ?_, by simp⟩, ⟨?_, by simp⟩, by simp, trivial⟩ <;> omega
  · simp only [segs3, mkSeg, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl) <;> simp only [n1, n2, n3] <;>
      refine ⟨?_, by omega, by first | exact trim_length_le _ _ | simp [dropZeros_length_le], by decide⟩
    · rw [r1]; exact hok.base
    · rw [r2]; exact alignUp_mod _ _ hP
    · rw [r3]; exact alignUp_mod _ _ hP

theorem pagePerm_of_segPerm {img : Image} {pb : Nat} {top : UInt64} {p : Nat} {pm : Perm}
    (h : Image.segPerm pb img.segments p = some pm) : img.pagePerm pb top p = pm := by
  simp [Image.pagePerm, h]

/-- After a successful link, every section `s`, with index `i`, of every object `o`, with index
`j`, has an address `A`. The image holds at `A` the section's bytes with its relocations applied,
every reference resolved by `resolve` for object `j`, followed by its zero fill. Every byte of it
lies on a page with the permissions of the section's kind, and code is never writable. -/
theorem link_section {cfg : Config} {objs : List Obj} {img : Image}
    (h : link cfg objs = .ok img) {j i : Nat} {o : Obj} {s : Section}
    (ho : objs[j]? = some o) (hs : o.sections[i]? = some s) :
    ∃ A X, secAddr (layout cfg objs) j i = some A ∧ A + s.size ≤ limit cfg ∧
      applyRelocs (resolve (layout cfg objs) objs j) (UInt64.ofNat A) i o.relocs s.bytes =
        some X ∧ X.length = s.bytes.length ∧
      ∀ k, k < s.size →
        (X ++ List.replicate s.bssSize 0)[k]? = some (img.byteAt (UInt64.ofNat (A + k))) ∧
        img.pagePerm cfg.pageBits cfg.stackTop ((A + k) / 2 ^ cfg.pageBits) = s.kind.perm := by
  have hok := link_ok h
  obtain ⟨T, R, W, e, hT, hR, hW, _, rfl⟩ := hok.out
  obtain ⟨hch, hal, bT, bR, bW⟩ := segs_facts hok hT hR hW
  obtain ⟨A, hA, hp⟩ := secAddr_spec (cfg := cfg) ho hs
  let segs := (segs3 cfg (layout cfg objs) T R W).filter (fun sg => 0 < sg.memSize)
  have hch' : Chain segs := hch.filter _
  have hal' : ∀ t ∈ segs, t.vaddr.toNat % 2 ^ cfg.pageBits = 0 := fun t ht =>
    (hal t (List.mem_filter.1 ht).1).1
  have hin : ∀ sg ∈ segs3 cfg (layout cfg objs) T R W, 0 < sg.memSize → sg ∈ segs :=
    fun sg hm h1 => List.mem_filter.2 ⟨hm, by simp [h1]⟩
  have hpos : ∀ b (B : List UInt8), 0 < B.length → 0 < (fill cfg b B).length := fun b B h => by
    obtain ⟨t, ht⟩ := fill_prefix cfg b B; rw [ht, List.length_append]; omega
  have key : ∃ Y, content (layout cfg objs) objs ⟨j, i, s, o.relocs⟩ A = some Y ∧
      ∀ k, k < s.size → Y[k]? = some (Image.segByte segs (UInt64.ofNat (A + k))) ∧
        Image.segPerm cfg.pageBits segs ((A + k) / 2 ^ cfg.pageBits) = some s.kind.perm := by
    have hp' := hp
    simp only [layout, List.mem_append] at hp'
    rcases hp' with (hp' | hp') | hp'
    · exact group_mem hT hp' (fill_prefix _ _ _) (tr := false)
        (fun h => hin _ (by simp [segs3, Group.perm]) (hpos _ _ h)) hch' hal' bT
    · exact group_mem hR hp' (fill_prefix _ _ _) (tr := false)
        (fun h => hin _ (by simp [segs3, Group.perm]) (hpos _ _ h)) hch' hal' bR
    · exact group_mem hW hp' (fill_prefix _ _ _) (tr := true)
        (fun h => hin _ (by simp [segs3, Group.perm]) (hpos _ _ h)) hch' hal' bW
  obtain ⟨Y, hY, hk⟩ := key
  simp only [content, Option.map_eq_some_iff] at hY
  obtain ⟨X, hX, rfl⟩ := hY
  have hpl := placed_mem hp
  have hbound : A + s.size ≤ limit cfg := by
    have hp' := hp
    have ho' := layout_order cfg objs
    have hf := hok.fits
    simp only [layout, List.mem_append] at hp' ho' hf
    rcases hp' with (hp' | hp') | hp' <;> have := (place_mem _ _ _ hp').2.2 <;>
      simp only [layout] at * <;> omega
  refine ⟨A, X, hA, hbound, hX, applyRelocs_length _ _ _ _ _ _ hX, fun k hk' => ?_⟩
  obtain ⟨h1, h2⟩ := hk k hk'
  exact ⟨h1, pagePerm_of_segPerm h2⟩

/-- The linked image is valid for an ABI with the linker's page size and stack top. Its segments
are page-aligned, non-empty, in address order on disjoint pages, below the stack, and never both
writable and executable. -/
theorem link_valid {isa : Isa} (abi : Abi isa) {cfg : Config} {objs : List Obj} {img : Image}
    (h : link cfg objs = .ok img) (hpb : abi.pageBits = cfg.pageBits)
    (hst : abi.stackTop = cfg.stackTop) : img.valid abi = true := by
  have hok := link_ok h
  obtain ⟨T, R, W, e, hT, hR, hW, _, rfl⟩ := hok.out
  obtain ⟨hch, hal, -⟩ := segs_facts hok hT hR hW
  obtain ⟨hs1, hs2, hs3⟩ := hok.stack
  have hsp : ∀ segs, Image.stackPages abi.pageBits ⟨segs, e, cfg.stackSize⟩ =
      stackPages cfg := by
    intro segs; simp [Image.stackPages, stackPages, hpb]
  have hsp' : ∀ segs, Image.stackPages cfg.pageBits ⟨segs, e, cfg.stackSize⟩ =
      stackPages cfg := by
    intro segs; simp [Image.stackPages, stackPages]
  simp only [Image.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨hs1, by rw [hst, hpb]; exact hs2⟩, by rw [hsp, hst, hpb]; exact hs3⟩, ?_⟩, ?_⟩
  · intro sg hm
    obtain ⟨hm, hpos⟩ := List.mem_filter.1 hm
    obtain ⟨a1, a2, a3, a4⟩ := hal sg hm
    simp only [decide_eq_true_eq] at hpos
    simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
      hpb]
    refine ⟨⟨⟨⟨hpos, a3⟩, a1⟩, ?_⟩, ?_⟩
    · cases hw : sg.perm.w <;> cases hx : sg.perm.x <;> simp_all
    · rw [hsp', hst]; exact a2
  · rw [hpb]
    exact sortedDisjoint_of_chain (hch.filter _) fun t ht =>
      ⟨(hal t (List.mem_filter.1 ht).1).1, by simpa using (List.mem_filter.1 ht).2⟩

/-- Code is never writable, since the linked image starts in W^X memory. -/
theorem link_wxorx {isa : Isa} (abi : Abi isa) {cfg : Config} {objs : List Obj} {img : Image}
    (h : link cfg objs = .ok img) (hpb : abi.pageBits = cfg.pageBits)
    (hst : abi.stackTop = cfg.stackTop) : (img.init abi).mem.WxorX :=
  Image.init_wxorx abi img (link_valid abi h hpb hst)

/-! ## Symbols -/

theorem find?_unique {α : Type} {p : α → Bool} {l : List α} {x : α} (hx : x ∈ l) (hp : p x)
    (hu : ∀ y ∈ l, p y → y = x) : l.find? p = some x := by
  cases hf : l.find? p with
  | none => rw [List.find?_eq_none] at hf; exact absurd hp (hf x hx)
  | some y => rw [hu y (List.mem_of_find?_eq_some hf) (List.find?_some hf)]

theorem inj_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, hn, x, y, hx, hy, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.1 hx with hx' | hx' <;> rcases List.mem_cons.1 hy with hy' | hy'
    · rw [hx', hy']
    · subst hx'; exact absurd ⟨y, hy', he.symm⟩ hn.1
    · subst hy'; exact absurd ⟨x, hx', he⟩ hn.1
    · exact inj_of_nodup_map hn.2 hx' hy' he

theorem find_name {l : List Symbol} {sym : Symbol} (hn : (l.map (·.name)).Nodup)
    (hm : sym ∈ l) : l.find? (fun s => s.name == sym.name) = some sym :=
  find?_unique hm (by simp) fun y hy hp => inj_of_nodup_map hn hy hm (by simpa using hp)

theorem mem_globalNames {objs : List Obj} {k : Nat} {o : Obj} {s : Symbol}
    (ho : objs[k]? = some o) (hs : s ∈ o.symbols) (hg : s.global = true) :
    s.name ∈ globalNames objs := by
  simp only [globalNames, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨o, List.mem_of_getElem? ho, s, ⟨hs, hg⟩, rfl⟩

theorem globalSym_spec : ∀ {objs : List Obj}, (globalNames objs).Nodup →
    ∀ {j0 k : Nat} {o : Obj} {sym : Symbol}, objs[k]? = some o → sym ∈ o.symbols →
      sym.global = true → globalSym sym.name j0 objs = some (j0 + k, sym)
  | [], _, _, _, _, _, ho, _, _ => by simp at ho
  | o' :: os, hn, j0, k, o, sym, ho, hs, hg => by
    have hn' : (((o'.symbols.filter (·.global)).map (·.name)) ++ globalNames os).Nodup := by
      simpa [globalNames] using hn
    rw [List.nodup_append] at hn'
    simp only [globalSym]
    cases k with
    | zero =>
      simp at ho; subst ho
      rw [find?_unique hs (by simp [hg]) fun y hy hp => by
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact inj_of_nodup_map hn'.1 (List.mem_filter.2 ⟨hy, hp.1⟩)
          (List.mem_filter.2 ⟨hs, hg⟩) hp.2]
      simp
    | succ k =>
      have ho' : os[k]? = some o := by simpa using ho
      have hnone : o'.symbols.find? (fun s => s.global && s.name == sym.name) = none := by
        rw [List.find?_eq_none]
        intro y hy hp
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact hn'.2.2 y.name (List.mem_map.2 ⟨y, List.mem_filter.2 ⟨hy, hp.1⟩, rfl⟩) sym.name
          (mem_globalNames ho' hs hg) hp.2
      rw [hnone, globalSym_spec hn'.2.1 ho' hs hg, show j0 + 1 + k = j0 + (k + 1) by omega]

theorem globalSym_mem {n : String} : ∀ {objs : List Obj} {j0 j : Nat} {s : Symbol},
    globalSym n j0 objs = some (j, s) →
    j0 ≤ j ∧ ∃ o, objs[j - j0]? = some o ∧ s ∈ o.symbols ∧ s.global = true ∧ s.name = n
  | [], _, _, _, h => by simp [globalSym] at h
  | o :: os, j0, j, s, h => by
    simp only [globalSym] at h
    split at h
    · rename_i y hy
      cases h
      have := List.find?_some hy
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨Nat.le_refl _, o, by simp, List.mem_of_find?_eq_some hy, this.1, this.2⟩
    · obtain ⟨h1, o', h2, h3⟩ := globalSym_mem h
      refine ⟨by omega, o', ?_, h3⟩
      rw [show j - j0 = (j - (j0 + 1)) + 1 by omega]; simpa using h2

/-- After a successful link, every symbol of object `j` resolves, for references from object `j`,
to its section's address plus its offset. A global symbol resolves to the same address from every
object. -/
theorem link_symbol {cfg : Config} {objs : List Obj} {img : Image}
    (h : link cfg objs = .ok img) {j : Nat} {o : Obj} {sym : Symbol}
    (ho : objs[j]? = some o) (hsym : sym ∈ o.symbols) :
    ∃ A, secAddr (layout cfg objs) j sym.sec = some A ∧
      resolve (layout cfg objs) objs j sym.name = some (UInt64.ofNat (A + sym.offset)) ∧
      (sym.global = true →
        globalAddr (layout cfg objs) objs sym.name = some (UInt64.ofNat (A + sym.offset))) := by
  have hok := link_ok h
  have hom := List.mem_of_getElem? ho
  have hsec := hok.symSec o hom sym hsym
  obtain ⟨s, hs⟩ : ∃ s, o.sections[sym.sec]? = some s := ⟨_, List.getElem?_eq_getElem hsec⟩
  obtain ⟨A, hA, -⟩ := secAddr_spec (cfg := cfg) ho hs
  refine ⟨A, hA, ?_, fun hg => ?_⟩
  · simp only [resolve, ho, Option.bind_some, find_name (hok.names o hom) hsym, symAddr, hA,
      Option.map_some]
  · simp only [globalAddr, globalSym_spec hok.globals ho hsym hg, Nat.zero_add, symAddr, hA,
      Option.map_some]

/-- The entry point is the address of the global symbol `cfg.entry`, which resolves to it from the
object that defines it. -/
theorem link_entry {cfg : Config} {objs : List Obj} {img : Image}
    (h : link cfg objs = .ok img) :
    ∃ j o sym, objs[j]? = some o ∧ sym ∈ o.symbols ∧ sym.global = true ∧
      sym.name = cfg.entry ∧ globalAddr (layout cfg objs) objs cfg.entry = some img.entry ∧
      resolve (layout cfg objs) objs j cfg.entry = some img.entry := by
  have hok := link_ok h
  obtain ⟨T, R, W, e, -, -, -, he, rfl⟩ := hok.out
  have he' := he
  simp only [globalAddr] at he'
  split at he'
  · rename_i j sym hg
    obtain ⟨-, o, ho, hs, hgl, hn⟩ := globalSym_mem hg
    rw [Nat.sub_zero] at ho
    obtain ⟨A, _, hr, hga⟩ := link_symbol h ho hs
    refine ⟨j, o, sym, ho, hs, hgl, hn, he, ?_⟩
    rw [← hn, hr, ← hga hgl, hn, he]
  · cases he'

/-! ## In the initial machine state -/

theorem codeAt_of (m : Memory) : ∀ (bs : List UInt8) (a : UInt64),
    (∀ k (hk : k < bs.length), m.executable (a + UInt64.ofNat k) = true ∧
      m.bytes (a + UInt64.ofNat k) = bs[k]) → m.CodeAt a bs
  | [], _, _ => trivial
  | b :: bs, a, h => by
    have h0 := h 0 (by simp)
    have e0 : a + UInt64.ofNat 0 = a := by simp
    rw [e0] at h0
    refine ⟨h0.1, h0.2, codeAt_of m bs (a + 1) fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    rw [show a + 1 + UInt64.ofNat k = a + UInt64.ofNat (k + 1) by
      rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl]
    simpa using this

theorem read_of (m : Memory) : ∀ (bs : List UInt8) (a : UInt64),
    (∀ k (hk : k < bs.length), m.readable (a + UInt64.ofNat k) = true ∧
      m.bytes (a + UInt64.ofNat k) = bs[k]) → m.read a bs.length = some bs
  | [], _, _ => rfl
  | b :: bs, a, h => by
    have h0 := h 0 (by simp)
    have e0 : a + UInt64.ofNat 0 = a := by simp
    rw [e0] at h0
    have ih := read_of m bs (a + 1) fun k hk => by
      have := h (k + 1) (by simp; omega)
      rw [show a + 1 + UInt64.ofNat k = a + UInt64.ofNat (k + 1) by
        rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]; rfl]
      simpa using this
    simp only [List.length_cons, Memory.read, h0.1, ↓reduceIte, ih, Option.map_some, h0.2,
      List.getElem_cons_zero]

/-- The initial memory at a byte of a placed section is the section's byte, with its kind's
permissions. -/
theorem link_init_byte {isa : Isa} (abi : Abi isa) {cfg : Config} {objs : List Obj}
    {img : Image} (h : link cfg objs = .ok img) (hpb : abi.pageBits = cfg.pageBits)
    (hst : abi.stackTop = cfg.stackTop) {j i : Nat} {o : Obj} {s : Section}
    (ho : objs[j]? = some o) (hs : o.sections[i]? = some s) :
    ∃ A X, secAddr (layout cfg objs) j i = some A ∧ A + s.size < 2 ^ 64 ∧
      applyRelocs (resolve (layout cfg objs) objs j) (UInt64.ofNat A) i o.relocs s.bytes =
        some X ∧ X.length = s.bytes.length ∧
      ∀ k (hk : k < X.length),
        (img.init abi).mem.bytes (UInt64.ofNat A + UInt64.ofNat k) = X[k] ∧
        (img.init abi).mem.permAt (UInt64.ofNat A + UInt64.ofNat k) = s.kind.perm := by
  obtain ⟨A, X, hA, hb, hX, hXl, hk⟩ := link_section h ho hs
  have h64 := cfg.stackTop.toNat_lt
  have hl := limit_le cfg
  refine ⟨A, X, hA, by omega, hX, hXl, fun k hkx => ?_⟩
  have hks : k < s.size := by simp [Section.size]; omega
  obtain ⟨h1, h2⟩ := hk k hks
  have hak : (UInt64.ofNat (A + k)).toNat = A + k := by
    simp [UInt64.toNat_ofNat']; simp [Section.size] at hb; omega
  rw [← UInt64.ofNat_add]
  refine ⟨?_, ?_⟩
  · rw [List.getElem?_append_left hkx, List.getElem?_eq_getElem hkx] at h1
    exact (Option.some.inj h1).symm
  · simp only [Image.init, Image.mem, Memory.permAt, Memory.page, hak, hpb, hst]
    exact h2

/-- Every placed section starts at a multiple of its alignment. -/
theorem place_align : ∀ (cur : Nat) (its : List Item) (p : Item × Nat), p ∈ place cur its →
    0 < p.1.sec.align → p.2 % p.1.sec.align = 0
  | _, [], _, h, _ => by simp [place] at h
  | cur, it :: its, p, h, hp => by
    simp only [place, List.mem_cons] at h
    rcases h with rfl | h
    · exact alignUp_mod _ _ hp
    · exact place_align _ its p h hp

/-- A section's address is a multiple of its `align`. -/
theorem secAddr_align {cfg : Config} {objs : List Obj} {j i : Nat} {o : Obj} {s : Section}
    (ho : objs[j]? = some o) (hs : o.sections[i]? = some s) {A : Nat}
    (hA : secAddr (layout cfg objs) j i = some A) (hal : 0 < s.align) : A % s.align = 0 := by
  obtain ⟨A', hA', hm⟩ := secAddr_spec (cfg := cfg) ho hs
  rw [hA] at hA'; cases hA'
  simp only [layout, List.mem_append] at hm
  rcases hm with (hm | hm) | hm <;> exact place_align _ _ _ hm hal

end Millipede.Link

/-! ## Linking an assembled program loads it (every architecture) -/

namespace Millipede.Asm
open Millipede.Link

variable {A : Arch} {asm : Assembler A}

/-- Each data item sits in `.rodata` at its symbol's offset. -/
theorem asmData_spec : ∀ (ds : List (String × List UInt8)) (off : Nat),
    ∀ d ∈ ds, ∃ o, (⟨d.1, rodataSec, o, false⟩ : Symbol) ∈ (asmData off ds).2 ∧ off ≤ o ∧
      ∀ k, k < d.2.length → (asmData off ds).1[o - off + k]? = d.2[k]?
  | [], _, _, h => by simp at h
  | d' :: ds, off, d, h => by
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨off, by simp [asmData], Nat.le_refl _, fun k hk => ?_⟩
      simp only [asmData, Nat.sub_self, Nat.zero_add]
      rw [List.getElem?_append_left hk]
    · obtain ⟨o, hs, ho, hk⟩ := asmData_spec ds (off + d'.2.length) d h
      refine ⟨o, by simp [asmData, hs], by omega, fun k hkl => ?_⟩
      simp only [asmData]
      rw [List.getElem?_append_right (by omega), ← hk k hkl]
      congr 1; omega

theorem codeAt_append' (m : Memory) : ∀ (xs ys : List UInt8) (a : UInt64),
    m.CodeAt a (xs ++ ys) → m.CodeAt a xs ∧ m.CodeAt (a + UInt64.ofNat xs.length) ys
  | [], ys, a, h => ⟨trivial, by simpa using h⟩
  | x :: xs, ys, a, ⟨h1, h2, h3⟩ => by
    obtain ⟨c1, c2⟩ := codeAt_append' m xs ys (a + 1) h3
    refine ⟨⟨h1, h2, c1⟩, ?_⟩
    rw [show a + UInt64.ofNat (x :: xs).length = a + 1 + UInt64.ofNat xs.length by
      simp [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm 1]]
    exact c2

/-- The shape of an assembled object. -/
theorem assemble_shape {P : Prog A} {obj : Obj} (h : assemble asm P = .ok obj) :
    ∃ text relocs fsyms, asmFns asm 0 P.funs = .ok (text, relocs, fsyms) ∧
      obj = ⟨[⟨".text", .text, 16, text, 0⟩, ⟨".rodata", .rodata, 8, (asmData 0 P.data).1, 0⟩,
        ⟨".bss", .bss, 16, [], (asmBss 0 P.bss).1⟩],
        fsyms ++ (asmData 0 P.data).2 ++ (asmBss 0 P.bss).2, relocs⟩ := by
  obtain ⟨text, relocs, fsyms, hq, -, rfl⟩ := assemble_inv h
  exact ⟨text, relocs, fsyms, hq, rfl⟩

theorem ofNat_add_add (A o k : Nat) :
    UInt64.ofNat (A + o) + UInt64.ofNat k = UInt64.ofNat A + UInt64.ofNat (o + k) := by
  simp [UInt64.ofNat_add, UInt64.add_assoc]

/-- Linking an assembled program loads it. If `assemble P = .ok obj` and
`link cfg [obj] = .ok img`, then in the initial state `img.init abi`, for an ABI with the linker's
page size and stack top, `P` is loaded under the linker's symbol resolution `σ`. Every function's
resolved code sits executable at its symbol, and every data item sits readable and not writable
at its symbol. The memory is W^X, and a function named `cfg.entry` is where execution starts. -/
theorem link_assemble (hl : asm.Laws) {P : Prog A} {obj : Obj} (hA : assemble asm P = .ok obj)
    {cfg : Config} {img : Image} (hL : link cfg [obj] = .ok img) (abi : Abi A.isa)
    (hpb : abi.pageBits = cfg.pageBits) (hst : abi.stackTop = cfg.stackTop) :
    P.Loaded (resolve (layout cfg [obj]) [obj] 0) (img.init abi).mem ∧
      (img.init abi).mem.WxorX ∧
      ∀ f ∈ P.funs, f.name = cfg.entry →
        resolve (layout cfg [obj]) [obj] 0 f.name = some img.entry := by
  let σ := resolve (layout cfg [obj]) [obj] 0
  obtain ⟨text, relocs, fsyms, hfns, hobj⟩ := assemble_shape hA
  have ho : [obj][0]? = some obj := rfl
  refine ⟨⟨?_, ?_⟩, link_wxorx abi hL hpb hst, ?_⟩
  · -- functions
    obtain ⟨text', hsec, _, hlaw⟩ := assemble_text hl hA
    obtain ⟨A, X, hA0, hb, hX, hXl, hk⟩ := link_init_byte abi hL hpb hst ho hsec
    dsimp only at hXl
    have hb' : A + text'.length < 2 ^ 64 := by simpa [Section.size] using hb
    have hw : (UInt64.ofNat A).toNat + text'.length < 2 ^ 64 := by
      simp [UInt64.toNat_ofNat']; omega
    intro f hf
    obtain ⟨o, code, hsym, hcode, hpre⟩ := (hlaw σ _ X hw hX).2 f hf
    obtain ⟨A', hA', hres, -⟩ := link_symbol hL ho hsym
    rw [hA0] at hA'; cases hA'
    refine ⟨UInt64.ofNat (A + o), code, hres, by rw [UInt64.ofNat_add]; exact hcode, ?_⟩
    obtain ⟨t, ht⟩ := hpre
    apply codeAt_of
    intro k hkc
    have hlen : o + k < X.length := by
      have := congrArg List.length ht; simp at this; omega
    obtain ⟨h1, h2⟩ := hk (o + k) (by omega)
    rw [ofNat_add_add]
    refine ⟨by simp only [Memory.executable, h2]; rfl, ?_⟩
    rw [h1]
    have := congrArg (·[k]?) ht
    simp only [List.getElem?_append_left hkc, List.getElem?_drop] at this
    rw [List.getElem?_eq_getElem hkc, List.getElem?_eq_getElem (by omega)] at this
    exact (Option.some.inj this).symm
  · -- data
    intro d hd
    have hsec : obj.sections[rodataSec]? =
        some ⟨".rodata", .rodata, 8, (asmData 0 P.data).1, 0⟩ := by rw [hobj]; rfl
    obtain ⟨A, X, hA1, hb, hX, hXl, hk⟩ := link_init_byte abi hL hpb hst ho hsec
    have hrel : ∀ r ∈ obj.relocs, r.sec ≠ rodataSec := by
      intro r hr
      rw [hobj] at hr
      rw [asmFns_relocs hl _ _ _ _ _ hfns r hr]; decide
    rw [applyRelocs_other _ _ _ _ _ hrel] at hX
    cases hX
    obtain ⟨o, hsym, -, hdat⟩ := asmData_spec P.data 0 d hd
    have hsym' : (⟨d.1, rodataSec, o, false⟩ : Symbol) ∈ obj.symbols := by
      rw [hobj]; exact List.mem_append_left _ (List.mem_append_right _ hsym)
    obtain ⟨A', hA', hres, -⟩ := link_symbol hL ho hsym'
    rw [hA1] at hA'; cases hA'
    have hin : ∀ k, k < d.2.length → o + k < (asmData 0 P.data).1.length := by
      intro k hk'
      have := hdat k hk'
      rw [List.getElem?_eq_getElem hk', Nat.sub_zero] at this
      exact (List.getElem?_eq_some_iff.1 this).1
    dsimp only at hXl
    refine ⟨UInt64.ofNat (A + o), hres, ?_, fun i hi => ?_⟩
    · apply read_of
      intro k hkd
      have := hin k hkd
      obtain ⟨h1, h2⟩ := hk (o + k) (by omega)
      rw [ofNat_add_add]
      refine ⟨by simp only [Memory.readable, h2]; rfl, ?_⟩
      rw [h1]
      have := hdat k hkd
      simp only [Nat.sub_zero] at this
      rw [List.getElem?_eq_getElem hkd, List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    · have := hin i hi
      obtain ⟨-, h2⟩ := hk (o + i) (by omega)
      rw [ofNat_add_add]
      simp only [Memory.writable, h2]; rfl
  · intro f hf hn
    obtain ⟨j, o, sym, hj, -, -, -, -, hr⟩ := link_entry hL
    have hj0 : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact h
      · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
    subst hj0
    rw [hn]; exact hr

/-- Each zero-initialised region sits in `.bss` at its symbol's offset, inside the section. -/
theorem asmBss_spec : ∀ (bs : List (String × Nat)) (off : Nat),
    off ≤ (asmBss off bs).1 ∧ ∀ b ∈ bs, ∃ o, (⟨b.1, bssSec, o, false⟩ : Symbol) ∈ (asmBss off bs).2 ∧
      o + b.2 ≤ (asmBss off bs).1
  | [], off => ⟨Nat.le_refl _, fun _ h => by simp at h⟩
  | b' :: bs, off => by
    have ih := asmBss_spec bs ((off + 15) / 16 * 16 + b'.2)
    have hr : off ≤ (off + 15) / 16 * 16 := by
      have := Nat.div_add_mod (off + 15) 16
      have := Nat.mod_lt (off + 15) (show 0 < 16 by decide)
      omega
    refine ⟨by simp only [asmBss]; omega, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨(off + 15) / 16 * 16, by simp [asmBss], by simp only [asmBss]; omega⟩
    · obtain ⟨o, hs, ho⟩ := ih.2 b hb
      exact ⟨o, by simp [asmBss, hs], by simpa [asmBss] using ho⟩

/-- After `assemble` and `link`, in the initial state of the image, each region of `P.bss` sits at
its symbol, readable, writable and zero, and ends at or below the linker's stack limit, which is
below the stack. -/
theorem link_assemble_bss {P : Prog A} {obj : Obj} (hA : assemble asm P = .ok obj)
    {cfg : Config} {img : Image} (hL : link cfg [obj] = .ok img) (abi : Abi A.isa)
    (hpb : abi.pageBits = cfg.pageBits) (hst : abi.stackTop = cfg.stackTop) :
    P.BssAt (resolve (layout cfg [obj]) [obj] 0) (img.init abi).mem ∧
      ∀ b ∈ P.bss, ∀ D, resolve (layout cfg [obj]) [obj] 0 b.1 = some D →
        D.toNat + b.2 ≤ limit cfg := by
  obtain ⟨text, relocs, fsyms, hfns, hobj⟩ := assemble_shape hA
  have ho : [obj][0]? = some obj := rfl
  have hsec : obj.sections[bssSec]? = some ⟨".bss", .bss, 16, [], (asmBss 0 P.bss).1⟩ := by
    rw [hobj]; rfl
  obtain ⟨A, X, hA2, hb, hX, hXl, hk⟩ := link_section hL ho hsec
  have hX0 : X = [] := List.eq_nil_of_length_eq_zero hXl
  subst hX0
  have h64 := cfg.stackTop.toNat_lt
  have hl := limit_le cfg
  have hspec := asmBss_spec P.bss 0
  have key : ∀ b ∈ P.bss, ∃ o, resolve (layout cfg [obj]) [obj] 0 b.1 =
      some (UInt64.ofNat (A + o)) ∧ o + b.2 ≤ (asmBss 0 P.bss).1 := by
    intro b hb
    obtain ⟨o, hs, hle⟩ := hspec.2 b hb
    have hsym : (⟨b.1, bssSec, o, false⟩ : Symbol) ∈ obj.symbols := by
      rw [hobj]; exact List.mem_append_right _ hs
    obtain ⟨A', hA', hres, -⟩ := link_symbol hL ho hsym
    rw [hA2] at hA'; cases hA'
    exact ⟨o, hres, hle⟩
  simp only [Section.size, List.length_nil, Nat.zero_add] at hb hk
  refine ⟨fun b hb' => ?_, fun b hb' D hD => ?_⟩
  · obtain ⟨o, hres, hle⟩ := key b hb'
    refine ⟨_, hres, fun i hi => ?_⟩
    obtain ⟨h1, h2⟩ := hk (o + i) (by omega)
    have hak : (UInt64.ofNat (A + (o + i))).toNat = A + (o + i) := by
      simp [UInt64.toNat_ofNat']; omega
    have e : UInt64.ofNat (A + o) + UInt64.ofNat i = UInt64.ofNat (A + (o + i)) := by
      simp [UInt64.ofNat_add, UInt64.add_assoc]
    have hperm : (img.init abi).mem.permAt (UInt64.ofNat (A + (o + i))) = Perm.rw := by
      simp only [Image.init, Image.mem, Memory.permAt, Memory.page, hak, hpb, hst]
      exact h2
    rw [e]
    refine ⟨by simp only [Memory.readable, hperm]; rfl, by simp only [Memory.writable, hperm]; rfl,
      ?_⟩
    simp only [List.nil_append, List.getElem?_replicate] at h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))] at h1
    exact (Option.some.inj h1).symm
  · obtain ⟨o, hres, hle⟩ := key b hb'
    rw [hres] at hD; cases hD
    simp [UInt64.toNat_ofNat']; omega

theorem seqSize_dvd {k : Nat} (hk : ∀ i, k ∣ A.size i) : ∀ is : List A.SInstr, k ∣ seqSize A is
  | [] => Nat.dvd_zero k
  | i :: is => Nat.dvd_add (hk i) (seqSize_dvd hk is)

/-- With every instruction size a multiple of `k`, `asmFns` from an offset that is a multiple
of `k` puts every function's symbol at a multiple of `k`. -/
theorem asmFns_dvd (hl : asm.Laws) {k : Nat} (hk : ∀ i, k ∣ A.size i) :
    ∀ (fs : List (Fn A)) (off : Nat) (bs : List UInt8) (rs : List Reloc) (ss : List Symbol),
      asmFns asm off fs = .ok (bs, rs, ss) → k ∣ off →
      ∀ f ∈ fs, ∃ o, (⟨f.name, textSec, o, true⟩ : Symbol) ∈ ss ∧ k ∣ o
  | [], _, _, _, _, _, _, f, hf => by simp at hf
  | g :: fs, off, bs, rs, ss, h, hoff, f, hf => by
    obtain ⟨bf, rf, bs', rs', ss', hp, hq, -, -, rfl⟩ := asmFns_cons_inv h
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨off, List.mem_cons_self, hoff⟩
    · have hb : k ∣ off + bf.length := by
        rw [asmSeq_length hl _ _ _ _ hp]; exact Nat.dvd_add hoff (seqSize_dvd hk _)
      obtain ⟨o, hs, ho⟩ := asmFns_dvd hl hk fs _ _ _ _ hq hb f hf
      exact ⟨o, List.mem_cons_of_mem _ hs, ho⟩

/-- Function symbols are aligned. If every instruction's size is a multiple of `k`, and `k` divides
16, the alignment of `.text`, the linker places every function of an assembled program at a
multiple of `k`. -/
theorem link_fn_dvd (hl : asm.Laws) {k : Nat} (hk : ∀ i, k ∣ A.size i) (h16 : k ∣ 16)
    {P : Prog A} {obj : Obj} (hA : assemble asm P = .ok obj) {cfg : Config} {img : Image}
    (hL : link cfg [obj] = .ok img) :
    ∀ f ∈ P.funs, ∀ a, resolve (layout cfg [obj]) [obj] 0 f.name = some a → k ∣ a.toNat := by
  intro f hf a ha
  obtain ⟨text, relocs, fsyms, hq, -, hobj⟩ := assemble_inv hA
  obtain ⟨o, hs, hko⟩ := asmFns_dvd hl hk _ 0 _ _ _ hq (Nat.dvd_zero k) f hf
  have hsym : (⟨f.name, textSec, o, true⟩ : Symbol) ∈ obj.symbols := by
    rw [hobj]; exact List.mem_append_left _ (List.mem_append_left _ hs)
  have hsec : obj.sections[textSec]? = some ⟨".text", .text, 16, text, 0⟩ := by rw [hobj]; rfl
  have ho : [obj][0]? = some obj := rfl
  obtain ⟨T, hT, hres, -⟩ := link_symbol hL ho hsym
  have hal := secAddr_align ho hsec hT (Nat.zero_lt_succ 15)
  rw [hres] at ha; cases ha
  rw [UInt64.toNat_ofNat', Nat.dvd_mod_iff (Nat.dvd_trans h16 (by decide))]
  exact Nat.dvd_add (Nat.dvd_trans h16 (Nat.dvd_of_mod_eq_zero hal)) hko

end Millipede.Asm

/-! ## x64 -/

namespace Millipede.X64
open Millipede.Link

/-- `Asm.link_assemble` for x64. -/
theorem link_assemble {P : Asm.Prog arch} {obj : Obj} (hA : assemble P = .ok obj)
    {cfg : Config} {img : Image} (hL : link cfg [obj] = .ok img) (abi : Abi isa)
    (hpb : abi.pageBits = cfg.pageBits) (hst : abi.stackTop = cfg.stackTop) :
    P.Loaded (resolve (layout cfg [obj]) [obj] 0) (img.init abi).mem ∧
      (img.init abi).mem.WxorX ∧
      ∀ f ∈ P.funs, f.name = cfg.entry →
        resolve (layout cfg [obj]) [obj] 0 f.name = some img.entry :=
  Asm.link_assemble asmLaws hA hL abi hpb hst

/-- `Asm.link_assemble_bss` for x64. -/
theorem link_assemble_bss {P : Asm.Prog arch} {obj : Obj} (hA : assemble P = .ok obj)
    {cfg : Config} {img : Image} (hL : link cfg [obj] = .ok img) (abi : Abi isa)
    (hpb : abi.pageBits = cfg.pageBits) (hst : abi.stackTop = cfg.stackTop) :
    P.BssAt (resolve (layout cfg [obj]) [obj] 0) (img.init abi).mem ∧
      ∀ b ∈ P.bss, ∀ D, resolve (layout cfg [obj]) [obj] 0 b.1 = some D →
        D.toNat + b.2 ≤ limit cfg :=
  Asm.link_assemble_bss hA hL abi hpb hst

end Millipede.X64
