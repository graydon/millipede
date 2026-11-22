import Millipede.Object.ElfRel.Write
import Millipede.Object.ElfRel.Read
import Millipede.Object.LinkProof

/-!
# Laws of the ELF64 relocatable-object format

`read_write` says that the reader gives back every object the writer accepts, up to the order of
its symbols: `write m o = .ok bs` implies `read m bs = some o.norm`, where `o.norm` lists the
local symbols of `o` before its global ones and is otherwise `o`. `link_norm` says that the order
of symbols does not change what `link` does, and `link_read_write` combines the two: linking the
objects read back from written files gives exactly what linking the original objects gives.

The proof of `read_write` follows the reader step by step. `Good` collects what a successful
`write` checked. The written section headers are three runs, the `Obj`'s sections, the four fixed
sections and the relocation sections (`allHdrs_split`), and `hdrAt` gives the header of each
output section with the offset at which the file holds its contents. These laws cover the
reader model only: what a system linker does with the file is not modelled.
-/

namespace Millipede.ElfRel

open Elf (fits zeros zeros_length)

/-! ### Placing contents in the file -/

theorem lay_length : ∀ (cur : Nat) (os : List Out), cur + (lay cur os).length = layEnd cur os
  | _, [] => rfl
  | cur, o :: os => by
    have h1 := Link.le_alignUp cur o.align
    have h2 := lay_length (Link.alignUp cur o.align + o.bytes.length) os
    simp only [lay, layEnd, List.length_append, zeros_length]
    omega

@[simp] theorem mkHdrs_length : ∀ (cur : Nat) (ns : List Nat) (os : List Out),
    (mkHdrs cur ns os).length = min ns.length os.length
  | _, [], _ => by simp [mkHdrs]
  | _, _ :: _, [] => by simp [mkHdrs]
  | cur, _ :: ns, _ :: os => by
    simp [mkHdrs, mkHdrs_length _ ns os, Nat.succ_min_succ]

theorem mem_mkHdrs : ∀ {cur : Nat} {ns : List Nat} {os : List Out} {h : Shdr},
    h ∈ mkHdrs cur ns os → ∃ o ∈ os, ∃ n off, h = o.hdr n off
  | _, [], _, _, hm => by simp [mkHdrs] at hm
  | _, _ :: _, [], _, hm => by simp [mkHdrs] at hm
  | cur, n :: ns, o :: os, h, hm => by
    simp only [mkHdrs, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨o, by simp, n, _, rfl⟩
    · obtain ⟨o', ho', n', off', rfl⟩ := mem_mkHdrs hm
      exact ⟨o', by simp [ho'], n', off', rfl⟩

/-- The header of the section at index `i` names the offset at which the file holds its
contents. -/
theorem mkHdrs_getElem : ∀ (pre post : List UInt8) (cur : Nat) (ns : List Nat) (os : List Out),
    pre.length = cur → ∀ i (hn : i < ns.length) (ho : i < os.length), ∃ off,
      (mkHdrs cur ns os)[i]? = some (os[i].hdr ns[i] off) ∧
      off + os[i].bytes.length ≤ (pre ++ lay cur os ++ post).length ∧
      ((pre ++ lay cur os ++ post).drop off).take os[i].bytes.length = os[i].bytes
  | _, _, _, [], _, _, _, hn, _ => by simp at hn
  | _, _, _, _ :: _, [], _, _, _, ho => by simp at ho
  | pre, post, cur, n :: ns, o :: os, hpre, i, hn, ho => by
    cases i with
    | zero =>
      refine ⟨Link.alignUp cur o.align, by simp [mkHdrs], ?_, ?_⟩
      · have h1 := Link.le_alignUp cur o.align
        simp only [lay, List.length_append, zeros_length, List.getElem_cons_zero]
        omega
      · have e : pre ++ lay cur (o :: os) ++ post =
            (pre ++ zeros (Link.alignUp cur o.align - cur)) ++
              (o.bytes ++ (lay (Link.alignUp cur o.align + o.bytes.length) os ++ post)) := by
          simp [lay]
        have hl : (pre ++ zeros (Link.alignUp cur o.align - cur)).length = Link.alignUp cur o.align := by
          have h1 := Link.le_alignUp cur o.align
          simp only [List.length_append, zeros_length]; omega
        simp only [List.getElem_cons_zero]
        rw [e, List.drop_left' hl, List.take_left' rfl]
    | succ i =>
      have hl : (pre ++ (zeros (Link.alignUp cur o.align - cur) ++ o.bytes)).length =
          Link.alignUp cur o.align + o.bytes.length := by
        have h1 := Link.le_alignUp cur o.align
        simp only [List.length_append, zeros_length]; omega
      obtain ⟨off, h1, h2, h3⟩ := mkHdrs_getElem (pre ++ (zeros (Link.alignUp cur o.align - cur) ++
        o.bytes)) post _ ns os hl i (by simpa using hn) (by simpa using ho)
      refine ⟨off, by simpa [mkHdrs] using h1, ?_, ?_⟩
      · simpa [lay, List.append_assoc] using h2
      · simpa [lay, List.append_assoc] using h3

theorem mkHdrs_append : ∀ (cur : Nat) (ns : List Nat) (A B : List Out), A.length ≤ ns.length →
    mkHdrs cur ns (A ++ B) = mkHdrs cur ns A ++ mkHdrs (layEnd cur A) (ns.drop A.length) B
  | _, _, [], _, _ => by cases ‹List Nat› <;> simp [mkHdrs, layEnd]
  | _, [], _ :: _, _, h => by simp at h
  | cur, n :: ns, o :: A, B, h => by
    simp only [List.cons_append, mkHdrs, layEnd, List.length_cons, List.drop_succ_cons,
      List.cons.injEq, true_and]
    exact mkHdrs_append _ ns A B (by simpa using h)

theorem lay_append : ∀ (cur : Nat) (A B : List Out),
    lay cur (A ++ B) = lay cur A ++ lay (layEnd cur A) B
  | _, [], _ => by simp [lay, layEnd]
  | cur, o :: A, B => by
    simp [lay, layEnd, lay_append _ A B]

/-! ### Names, runs and addends -/

theorem not_mem_of_noNul {s : String} (h : noNul s = true) : (0 : UInt8) ∉ strBytes s := by
  simpa [noNul] using h

/-- Every name of a string table built from `ns` is read back at its offset. -/
theorem strAt_strtab (ns : List String) (h : ∀ s ∈ ns, noNul s = true) (i : Nat)
    (hi : i < ns.length) :
    strAt (strtab (ns.map strBytes)) ((strOffs 1 (ns.map strBytes))[i]'(by simpa)) = some ns[i] := by
  have := cstr_strtab (ns.map strBytes) [0] [] (by
    intro b hb
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
    exact not_mem_of_noNul (h s hs)) i (by simpa)
  simp only [List.append_nil, List.length_singleton] at this
  simp only [strAt, strtab, List.singleton_append] at this ⊢
  rw [this]
  simp [ofBytes_strBytes]

theorem strOffs_ge : ∀ (cur : Nat) (ns : List (List UInt8)), ∀ x ∈ strOffs cur ns, cur ≤ x
  | _, [] => by simp [strOffs]
  | cur, n :: ns => by
    intro x hx
    simp only [strOffs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · have := strOffs_ge _ ns x hx; omega

theorem mem_dedup : ∀ {l : List String} {x : String}, x ∈ dedup l ↔ x ∈ l
  | [], _ => by simp [dedup]
  | y :: l, x => by
    simp only [dedup, List.mem_cons, List.mem_filter, mem_dedup, bne_iff_ne, ne_eq]
    by_cases h : x = y <;> simp [h]

theorem runs_flatten : ∀ rs : List Reloc, ((runs rs).map (·.2)).flatten = rs
  | [] => rfl
  | r :: rs => by
    have ih := runs_flatten rs
    simp only [runs]
    split
    · rename_i s g tl e
      rw [e] at ih
      split <;> simp_all
    · rename_i e
      rw [e] at ih
      simp_all

theorem runs_sec : ∀ (rs : List Reloc), ∀ p ∈ runs rs, ∀ r ∈ p.2, r.sec = p.1
  | [] => by simp [runs]
  | r :: rs => by
    have ih := runs_sec rs
    simp only [runs]
    split
    · rename_i s g tl e
      rw [e] at ih
      split
      · rename_i hs
        intro p hp x hx
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hs.symm
          · exact ih (s, g) (by simp) x hx
        · exact ih p (by simp [hp]) x hx
      · intro p hp x hx
        simp only [List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · simp at hx; simp [hx]
        · exact ih _ (by simp) x hx
        · exact ih p (by simp [hp]) x hx
    · intro p hp x hx
      simp at hp; subst hp; simp at hx; simp [hx]

theorem mem_of_mem_runs {rs : List Reloc} {p : Nat × List Reloc} (hp : p ∈ runs rs) {r : Reloc}
    (hr : r ∈ p.2) : r ∈ rs := by
  rw [← runs_flatten rs]
  exact List.mem_flatten.mpr ⟨p.2, List.mem_map.mpr ⟨p, hp, rfl⟩, hr⟩

theorem runs_ne_nil : ∀ (rs : List Reloc), ∀ p ∈ runs rs, p.2 ≠ []
  | [] => by simp [runs]
  | r :: rs => by
    have ih := runs_ne_nil rs
    simp only [runs]
    split
    · rename_i s g tl e
      rw [e] at ih
      split
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · exact ih p (by simp [hp])
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · simp
        · exact ih _ (by simp)
        · exact ih p (by simp [hp])
    · intro p hp; simp at hp; subst hp; simp

theorem signed64_addendBits {a : Int} (h1 : -2 ^ 63 ≤ a) (h2 : a < 2 ^ 63) :
    signed64 (addendBits a) = a := by
  unfold signed64 addendBits
  split <;> omega

/-! ### What a successful write checked -/

/-- The checks of `write`, one fact per field. -/
structure Good (m : Mach) (o : Obj) : Prop where
  kinds : ∀ r ∈ o.relocs, (m.relType r.kind).isSome = true
  rsec : ∀ r ∈ o.relocs, r.sec < o.sections.length
  addend : ∀ r ∈ o.relocs, -2 ^ 63 ≤ r.addend ∧ r.addend < 2 ^ 63
  secs : ∀ s ∈ o.sections, secOk s = true
  ssec : ∀ s ∈ o.symbols, s.sec < o.sections.length
  names : (o.symbols.map (·.name)).Nodup
  runs : ((runs o.relocs).map (·.1)).Nodup
  secNames : ∀ s ∈ secNames m o, noNul s = true
  symNames : ∀ s ∈ symNames o, noNul s = true ∧ s ≠ ""
  ehdr : (ehdr m o).fits = true
  shnum : (outs m o).length + 1 < SHN_LORESERVE
  hdrs : ∀ h ∈ hdrs m o, fitsW shdrW h.toList = true
  syms : ∀ s ∈ symEnts o, fitsW symW s.toList = true
  relas : ∀ r ∈ o.relocs, fitsW relaW (relaEnt m o r) = true

theorem good_of_write {m : Mach} {o : Obj} {bs : List UInt8} (h : write m o = .ok bs) :
    Good m o ∧ bs = fileBytes m o := by
  unfold write at h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  rename_i h1 h2
  simp only [Bool.not_eq_false, objOk, fieldsOk, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at h1 h2
  obtain ⟨⟨⟨⟨⟨⟨hr, hs⟩, hy⟩, hn⟩, hu⟩, hsn⟩, hyn⟩ := h1
  obtain ⟨⟨⟨⟨he, hsh⟩, hh⟩, hsy⟩, hre⟩ := h2
  exact ⟨⟨fun r m => (hr r m).1.1, fun r m => (hr r m).1.2, fun r m => (hr r m).2, hs, hy, hn, hu,
    hsn, fun s m => ⟨(hyn s m).1, (hyn s m).2⟩, he, hsh, hh, hsy, hre⟩, rfl⟩

/-! ### The shape of the written file -/

/-- The class of an output section's header. -/
def Out.cls (x : Out) : Cls := clsOf x.type x.flags

@[simp] theorem Out.hdr_cls (x : Out) (n off : Nat) : (x.hdr n off).cls = x.cls := rfl
@[simp] theorem Out.hdr_type (x : Out) (n off : Nat) : (x.hdr n off).type = x.type := rfl

theorem secOut_cls (s : Section) : (secOut s).cls = .sec s.kind := by
  cases h : s.kind <;> simp [secOut, h, Out.cls] <;> decide

theorem relaOut_cls (m : Mach) (o : Obj) (p : Nat × List Reloc) : (relaOut m o p).cls = .rela := by
  simp only [relaOut, Out.cls]; decide

/-- The offsets of the section names in `.shstrtab`. -/
def nameOffs (m : Mach) (o : Obj) : List Nat := strOffs 1 ((secNames m o).map strBytes)

/-- The headers after the null one. -/
def allHdrs (m : Mach) (o : Obj) : List Shdr := mkHdrs 64 (nameOffs m o) (outs m o)

section
variable {m : Mach} {o : Obj}

theorem names_outs : (outs m o).map (·.name) = secNames m o := by
  simp [outs, secNames, outsWith, fixedOuts, shstrOut]

theorem nameOffs_length : (nameOffs m o).length = (outs m o).length := by
  simp [nameOffs, ← names_outs]

theorem outs_length :
    (outs m o).length = o.sections.length + 4 + (runs o.relocs).length := by
  simp [outs, outsWith, fixedOuts]; omega

@[simp] theorem allHdrs_length : (allHdrs m o).length = (outs m o).length := by
  simp [allHdrs, nameOffs_length]

theorem hdrs_eq : hdrs m o = Shdr.null :: allHdrs m o := rfl

theorem fileBytes_eq : fileBytes m o = Elf.encodeEhdr (ehdr m o) ++ lay 64 (outs m o) ++
    (zeros (shoff m o - layEnd 64 (outs m o)) ++ encodeTab shdrW ((hdrs m o).map Shdr.toList)) := by
  simp [fileBytes]

theorem prefix_length : (Elf.encodeEhdr (ehdr m o) ++ lay 64 (outs m o) ++
    zeros (shoff m o - layEnd 64 (outs m o))).length = shoff m o := by
  have h1 := lay_length 64 (outs m o)
  have h2 := Link.le_alignUp (layEnd 64 (outs m o)) 8
  simp only [List.length_append, Elf.encodeEhdr_length, zeros_length, shoff, Elf.EHDR_SIZE]
  omega

theorem hdrs_fit (g : Good m o) : ((hdrs m o).map Shdr.toList).all (fitsW shdrW) = true := by
  simpa using g.hdrs

theorem fileBytes_length (g : Good m o) :
    (fileBytes m o).length = shoff m o + SHDR_SIZE * ((outs m o).length + 1) := by
  have := prefix_length (m := m) (o := o)
  rw [fileBytes, List.length_append, this, encodeTab_length _ _ (hdrs_fit g)]
  simp [hdrs_eq, shdrW_sum]

/-- Each output section's header names the offset of its contents in the file. -/
theorem outAt (i : Nat) (hi : i < (outs m o).length) : ∃ off,
    (allHdrs m o)[i]? = some ((outs m o)[i].hdr ((nameOffs m o)[i]'(by
      rw [nameOffs_length]; exact hi)) off) ∧
    off + (outs m o)[i].bytes.length ≤ (fileBytes m o).length ∧
    ((fileBytes m o).drop off).take (outs m o)[i].bytes.length = (outs m o)[i].bytes := by
  rw [fileBytes_eq]
  exact mkHdrs_getElem _ _ 64 _ _ (by simp [Elf.EHDR_SIZE]) i (by rw [nameOffs_length]; exact hi) hi

end

/-- The headers of the `Obj`'s sections. -/
def secHdrs (m : Mach) (o : Obj) : List Shdr := mkHdrs 64 (nameOffs m o) (o.sections.map secOut)

/-- The headers of the four fixed sections. -/
def fixHdrs (m : Mach) (o : Obj) : List Shdr :=
  mkHdrs (layEnd 64 (o.sections.map secOut)) ((nameOffs m o).drop o.sections.length)
    (fixedOuts o (shstrtab m o))

/-- The headers of the relocation sections. -/
def relHdrs (m : Mach) (o : Obj) : List Shdr :=
  mkHdrs (layEnd (layEnd 64 (o.sections.map secOut)) (fixedOuts o (shstrtab m o)))
    ((nameOffs m o).drop (o.sections.length + 4)) ((runs o.relocs).map (relaOut m o))

section
variable {m : Mach} {o : Obj}

/-- The headers as three runs: the `Obj`'s sections, the four fixed ones and the relocation
sections. -/
theorem allHdrs_split : allHdrs m o = secHdrs m o ++ (fixHdrs m o ++ relHdrs m o) := by
  unfold secHdrs fixHdrs relHdrs
  have hl := nameOffs_length (m := m) (o := o)
  rw [outs_length] at hl
  rw [allHdrs, outs, outsWith, List.append_assoc,
    mkHdrs_append _ _ _ _ (by simp; omega), mkHdrs_append _ _ _ _ (by simp [fixedOuts]; omega)]
  simp [List.drop_drop, fixedOuts, Nat.add_comm]

theorem outs_sec {i : Nat} (hi : i < o.sections.length) :
    (outs m o)[i]? = some (secOut o.sections[i]) := by
  simp [outs, outsWith, List.getElem?_append_left, hi]

theorem outs_fix {k : Nat} (hk : k < 4) :
    (outs m o)[o.sections.length + k]? = (fixedOuts o (shstrtab m o))[k]? := by
  rw [outs, outsWith, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp [fixedOuts]; omega)]
  simp

theorem outs_rela {j : Nat} (hj : j < (runs o.relocs).length) :
    (outs m o)[o.sections.length + 4 + j]? = some (relaOut m o (runs o.relocs)[j]) := by
  rw [outs, outsWith, List.getElem?_append_right (by simp [fixedOuts])]
  simp [fixedOuts, hj]

/-- The header of output section `i`: its name, and its contents when it has any in the file. -/
theorem hdrAt (g : Good m o) {i : Nat} {x : Out} (hx : (outs m o)[i]? = some x) :
    ∃ nm off, (allHdrs m o)[i]? = some (x.hdr nm off) ∧ strAt (shstrtab m o) nm = some x.name ∧
      (x.size = x.bytes.length → contents (fileBytes m o) (x.hdr nm off) = some x.bytes) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨off, h1, h2, h3⟩ := outAt (m := m) (o := o) i hi
  refine ⟨_, off, h1, ?_, fun hs => ?_⟩
  · have hn : i < (secNames m o).length := by rw [← names_outs]; simpa using hi
    have := strAt_strtab (secNames m o) g.secNames i hn
    simp only [nameOffs, shstrtab]
    rw [this]
    simp [← names_outs]
  · simp only [contents, Out.hdr, hs, h2, ite_true, h3]

theorem nameOffs_length' : (nameOffs m o).length =
    o.sections.length + 4 + (runs o.relocs).length := by
  rw [nameOffs_length, outs_length]

@[simp] theorem secHdrs_length : (secHdrs m o).length = o.sections.length := by
  simp [secHdrs, nameOffs_length']; omega

@[simp] theorem fixHdrs_length : (fixHdrs m o).length = 4 := by
  simp only [fixHdrs, mkHdrs_length, List.length_drop, nameOffs_length', fixedOuts,
    List.length_cons, List.length_nil]
  omega

@[simp] theorem relHdrs_length : (relHdrs m o).length = (runs o.relocs).length := by
  simp [relHdrs, nameOffs_length']

theorem secHdrs_get {i : Nat} (hi : i < o.sections.length) :
    (secHdrs m o)[i]? = (allHdrs m o)[i]? := by
  rw [allHdrs_split, List.getElem?_append_left (by simpa using hi)]

theorem fixHdrs_get {k : Nat} (hk : k < 4) :
    (fixHdrs m o)[k]? = (allHdrs m o)[o.sections.length + k]? := by
  rw [allHdrs_split, List.getElem?_append_right (by simp), List.getElem?_append_left (by simpa)]
  simp

theorem relHdrs_get (j : Nat) :
    (relHdrs m o)[j]? = (allHdrs m o)[o.sections.length + 4 + j]? := by
  rw [allHdrs_split, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega)]
  simp only [secHdrs_length, fixHdrs_length]
  congr 1; omega

theorem secHdrs_cls {h : Shdr} (hh : h ∈ secHdrs m o) : ∃ k, h.cls = .sec k := by
  obtain ⟨x, hx, n, off, rfl⟩ := mem_mkHdrs hh
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨s.kind, by simp [secOut_cls]⟩

theorem relHdrs_cls {h : Shdr} (hh : h ∈ relHdrs m o) : h.cls = .rela := by
  obtain ⟨x, hx, n, off, rfl⟩ := mem_mkHdrs hh
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  simp [relaOut_cls]

theorem fixHdrs_cls {h : Shdr} (hh : h ∈ fixHdrs m o) :
    h.cls = .ignored ∨ h.cls = .symtab ∨ h.cls = .strtab := by
  obtain ⟨x, hx, n, off, rfl⟩ := mem_mkHdrs hh
  simp only [fixedOuts, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    simp only [Out.hdr_cls, Out.cls, noteOut, symOut, strOut, shstrOut] <;> decide

@[simp] theorem null_cls : Shdr.null.cls = .ignored := by decide

/-! ### Reading the sections -/

theorem loadSecs_append (bs sh : List UInt8) : ∀ {A B : List Shdr} {sa sb : List Section},
    loadSecs bs sh A = some sa → loadSecs bs sh B = some sb →
    loadSecs bs sh (A ++ B) = some (sa ++ sb)
  | [], _, sa, _, ha, hb => by cases ha; simpa using hb
  | h :: A, B, sa, sb, ha, hb => by
    simp only [loadSecs, List.cons_append] at ha ⊢
    split at ha
    · split at ha
      · rename_i s ss e1 e2
        cases ha
        rw [e1, loadSecs_append bs sh e2 hb]
        rfl
      · cases ha
    · exact loadSecs_append bs sh ha hb

theorem loadSecs_nosec (bs sh : List UInt8) : ∀ (l : List Shdr),
    (∀ h ∈ l, ∀ k, h.cls ≠ .sec k) → loadSecs bs sh l = some []
  | [], _ => rfl
  | h :: l, hl => by
    simp only [loadSecs]
    split
    · rename_i k e; exact absurd e (hl h (by simp) k)
    · exact loadSecs_nosec bs sh l (fun x hx => hl x (by simp [hx]))

theorem loadSecs_of (bs sh : List UInt8) : ∀ (l : List Shdr) (ss : List Section)
    (hl : l.length = ss.length),
    (∀ i (hi : i < l.length), ∃ k, l[i].cls = .sec k ∧
      loadSec bs sh k l[i] = some (ss[i]'(hl ▸ hi))) →
    loadSecs bs sh l = some ss
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl
  | h :: l, s :: ss, hl, H => by
    obtain ⟨k, hk, hs⟩ := H 0 (by simp)
    simp only [List.getElem_cons_zero] at hk hs
    simp only [loadSecs, hk, hs]
    rw [loadSecs_of bs sh l ss (by simpa using hl) (fun i hi => H (i + 1) (by simpa using hi))]

theorem loadSec_secOut (bs sh : List UInt8) {s : Section} {nm off : Nat} (hs : secOk s = true)
    (hn : strAt sh nm = some s.name)
    (hc : s.kind ≠ .bss → contents bs ((secOut s).hdr nm off) = some s.bytes) :
    loadSec bs sh s.kind ((secOut s).hdr nm off) = some s := by
  obtain ⟨name, kind, align, bytes, bss⟩ := s
  simp only [secOk, Bool.and_eq_true] at hs
  obtain ⟨⟨hk, ha⟩, hf⟩ := hs
  simp only at hn hc hk ha hf
  cases kind <;> simp only [List.isEmpty_iff, beq_iff_eq] at hk <;> subst hk <;>
    simp [loadSec, secOut, Out.hdr, ha, hn, hf] at hc ⊢ <;> exact hc

theorem loadSecs_hdrs (g : Good m o) :
    loadSecs (fileBytes m o) (shstrtab m o) (hdrs m o) = some o.sections := by
  rw [hdrs_eq, allHdrs_split]
  simp only [loadSecs, null_cls]
  have h1 : loadSecs (fileBytes m o) (shstrtab m o) (secHdrs m o) = some o.sections := by
    apply loadSecs_of _ _ _ _ (by simp)
    intro i hi
    have hi' : i < o.sections.length := by simpa using hi
    obtain ⟨nm, off, e1, e2, e3⟩ := hdrAt g (outs_sec (m := m) hi')
    have e : (secHdrs m o)[i] = (secOut o.sections[i]).hdr nm off := by
      have := secHdrs_get (m := m) (o := o) hi'
      rw [e1, List.getElem?_eq_getElem hi] at this
      exact Option.some.inj this
    rw [e]
    refine ⟨o.sections[i].kind, by simp [secOut_cls], ?_⟩
    have hn : (secOut o.sections[i]).name = o.sections[i].name := by
      cases h : o.sections[i].kind <;> simp [secOut, h]
    apply loadSec_secOut _ _ (g.secs _ (by simp)) (hn ▸ e2)
    intro hk
    have hb : (secOut o.sections[i]).bytes = o.sections[i].bytes := by
      cases h : o.sections[i].kind <;> simp_all [secOut]
    rw [← hb]
    apply e3
    cases h : o.sections[i].kind <;> simp_all [secOut]
  have h2 : loadSecs (fileBytes m o) (shstrtab m o) (fixHdrs m o ++ relHdrs m o) = some [] := by
    apply loadSecs_nosec
    intro h hh k hk
    rcases List.mem_append.mp hh with hh | hh
    · rcases fixHdrs_cls hh with e | e | e <;> rw [e] at hk <;> cases hk
    · rw [relHdrs_cls hh] at hk; cases hk
  simpa using loadSecs_append _ _ h1 h2

/-- The header of fixed section `k`. -/
theorem fixAt (g : Good m o) {k : Nat} (hk : k < 4) {x : Out}
    (hx : (fixedOuts o (shstrtab m o))[k]? = some x) :
    ∃ nm off, (hdrs m o)[o.sections.length + k + 1]? = some (x.hdr nm off) ∧
      (x.size = x.bytes.length → contents (fileBytes m o) (x.hdr nm off) = some x.bytes) := by
  obtain ⟨nm, off, e1, -, e3⟩ := hdrAt g ((outs_fix (m := m) (o := o) hk).trans hx)
  exact ⟨nm, off, by simpa [hdrs_eq] using e1, e3⟩

theorem strSec_strtab (g : Good m o) :
    strSec (fileBytes m o) (hdrs m o) (o.sections.length + 3) = some (strtabBytes o) := by
  obtain ⟨nm, off, e1, e2⟩ := fixAt g (k := 2) (x := strOut o) (by decide) (by simp [fixedOuts])
  rw [show o.sections.length + 3 = o.sections.length + 2 + 1 from rfl, strSec, e1]
  simp only [Out.hdr_type, show (strOut o).type = SHT_STRTAB from rfl, ite_true]
  exact e2 rfl

theorem strSec_shstrtab (g : Good m o) :
    strSec (fileBytes m o) (hdrs m o) (o.sections.length + 4) = some (shstrtab m o) := by
  obtain ⟨nm, off, e1, e2⟩ := fixAt g (k := 3) (x := shstrOut (shstrtab m o)) (by decide)
    (by simp [fixedOuts])
  rw [show o.sections.length + 4 = o.sections.length + 3 + 1 from rfl, strSec, e1]
  simp only [Out.hdr_type, show (shstrOut (shstrtab m o)).type = SHT_STRTAB from rfl, ite_true]
  exact e2 rfl

/-- The only symbol table is the one the writer made. -/
theorem symtab_filter (g : Good m o) : ∃ nm off,
    (hdrs m o).filter (·.cls = .symtab) = [(symOut o).hdr nm off] ∧
    contents (fileBytes m o) ((symOut o).hdr nm off) = some (symtabBytes o) := by
  obtain ⟨h0, h1, h2, h3, e⟩ : ∃ h0 h1 h2 h3, fixHdrs m o = [h0, h1, h2, h3] := by
    have := fixHdrs_length (m := m) (o := o)
    match fixHdrs m o, this with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  have get : ∀ k (hk : k < 4) (x : Out), (fixedOuts o (shstrtab m o))[k]? = some x →
      ∃ nm off, (fixHdrs m o)[k]? = some (x.hdr nm off) ∧
        (x.size = x.bytes.length → contents (fileBytes m o) (x.hdr nm off) = some x.bytes) := by
    intro k hk x hx
    obtain ⟨nm, off, e1, e2⟩ := fixAt g hk hx
    refine ⟨nm, off, ?_, e2⟩
    rw [fixHdrs_get hk, ← e1, hdrs_eq]
    simp [Nat.add_comm]
  obtain ⟨_, _, a0, -⟩ := get 0 (by decide) noteOut (by simp [fixedOuts])
  obtain ⟨nm, off, a1, c1⟩ := get 1 (by decide) (symOut o) (by simp [fixedOuts])
  obtain ⟨_, _, a2, -⟩ := get 2 (by decide) (strOut o) (by simp [fixedOuts])
  obtain ⟨_, _, a3, -⟩ := get 3 (by decide) (shstrOut (shstrtab m o))
    (by simp [fixedOuts])
  rw [e] at a0 a1 a2 a3
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at a0 a1 a2 a3
  subst a0 a1 a2 a3
  refine ⟨nm, off, ?_, c1 rfl⟩
  rw [hdrs_eq, allHdrs_split, e]
  have hs : (secHdrs m o).filter (·.cls = .symtab) = [] := by
    rw [List.filter_eq_nil_iff]
    intro h hh
    obtain ⟨k, hk⟩ := secHdrs_cls hh
    simp [hk]
  have hr : (relHdrs m o).filter (·.cls = .symtab) = [] := by
    rw [List.filter_eq_nil_iff]
    intro h hh
    simp [relHdrs_cls hh]
  have c0 : clsOf SHT_PROGBITS 0 = .ignored := by decide
  have c1 : clsOf SHT_SYMTAB 0 = .symtab := by decide
  have c2 : clsOf SHT_STRTAB 0 = .strtab := by decide
  simp [List.filter_append, hs, hr, Out.cls, c0, c1, c2, noteOut, symOut, strOut, shstrOut]

theorem table_of_contents {bs : List UInt8} {ws : List Nat} {h : Shdr} {es : List (List Nat)}
    (hc : contents bs h = some (encodeTab ws es)) (he : h.entsize = ws.sum) (hp : 0 < ws.sum)
    (hf : es.all (fitsW ws) = true) : table bs ws h = some es := by
  simp only [contents] at hc
  split at hc
  · rename_i hle
    have hx := Option.some.inj hc
    have hsz : h.size = ws.sum * es.length := by
      have := congrArg List.length hx
      rw [encodeTab_length ws es hf, List.length_take, List.length_drop] at this
      omega
    have hd : bs.drop h.offset = encodeTab ws es ++ (bs.drop h.offset).drop h.size := by
      rw [← hx, List.take_append_drop]
    unfold table
    rw [ite_eq_left_of_eq_true _ _ (by simp [he, hsz]; omega), hsz, Nat.mul_div_cancel_left _ hp, hd,
      decodeTab_encodeTab ws es hf]
  · cases hc

/-! ### Reading the symbols -/

theorem secHdrs_isSec {h : Shdr} (hh : h ∈ secHdrs m o) : h.isSec = true := by
  obtain ⟨k, hk⟩ := secHdrs_cls hh
  simp [Shdr.isSec, hk]

/-- ELF section `i + 1` is section `i` of the `Obj`. -/
theorem secIdx_hdrs {i : Nat} (hi : i < o.sections.length) :
    secIdx (hdrs m o) (i + 1) = some i := by
  have hi' : i < (secHdrs m o).length := by simpa using hi
  have e : (hdrs m o)[i + 1]? = some (secHdrs m o)[i] := by
    rw [hdrs_eq, List.getElem?_cons_succ, ← secHdrs_get hi, List.getElem?_eq_getElem hi']
  have ht : (hdrs m o).take (i + 1) = Shdr.null :: (secHdrs m o).take i := by
    rw [hdrs_eq, allHdrs_split, List.take_succ_cons, List.take_append_of_le_length (by omega)]
  have hc : ((secHdrs m o).take i).countP Shdr.isSec = i := by
    rw [List.countP_eq_length.mpr (fun x hx => secHdrs_isSec (List.mem_of_mem_take hx))]
    simp; omega
  unfold secIdx
  rw [e]
  simp only [secHdrs_isSec (List.getElem_mem hi'), ite_true, ht, List.countP_cons, hc]
  simp [Shdr.isSec, null_cls]

theorem readSyms_of (shs : List Shdr) (strs : List UInt8) : ∀ (k : Nat) (es : List Sym)
    (rs : List RSym) (hl : es.length = rs.length),
    (∀ i (hi : i < es.length), readSym shs strs (decide (i < k)) es[i] = some (rs[i]'(hl ▸ hi))) →
    readSyms shs strs k es = some rs
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, hl, _ | _, _ :: _, [], hl, _ => by simp at hl
  | k, e :: es, r :: rs, hl, H => by
    have h0 := H 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have hk : (k != 0) = decide (0 < k) := by cases k <;> simp
    rw [readSyms, hk, h0, readSyms_of shs strs (k - 1) es rs (by simpa using hl) (fun i hi => by
      have := H (i + 1) (by simpa using hi)
      rwa [show decide (i + 1 < k) = decide (i < k - 1) by simp; omega] at this)]

theorem symOffs_length : (symOffs o).length = (symNames o).length := by simp [symOffs]

theorem symOffs_pos {i : Nat} (hi : i < (symOffs o).length) : (symOffs o)[i] ≠ 0 := by
  have := strOffs_ge 1 _ _ (List.getElem_mem hi)
  simp only [symOffs] at this ⊢
  omega

theorem strAt_symOffs (g : Good m o) {i : Nat} (hi : i < (symOffs o).length) :
    strAt (strtabBytes o) (symOffs o)[i] = some ((symNames o)[i]'(by
      rw [← symOffs_length]; exact hi)) := by
  have := strAt_strtab (symNames o) (fun s hs => (g.symNames s hs).1) i
    (by rw [← symOffs_length]; exact hi)
  simpa [symOffs, strtabBytes] using this

theorem readSym_symEnt (g : Good m o) {strs : List UInt8} {s : Symbol} (hs : s ∈ o.symbols)
    {nm : Nat} (hnm : nm ≠ 0) (hn : strAt strs nm = some s.name) :
    readSym (hdrs m o) strs (!s.global) (symEnt o nm s) = some (.defn s) := by
  have hsec := secIdx_hdrs (m := m) (g.ssec s hs)
  obtain ⟨name, sec, offset, global⟩ := s
  simp only at hn hsec
  unfold readSym symEnt Sym.bind Sym.type
  cases global <;> simp only [Bool.not_false, Bool.not_true, ite_true, ite_false,
    Bool.false_eq_true] <;>
    split <;> simp [STB_LOCAL, STB_GLOBAL, STT_FUNC, STT_OBJECT, STT_SECTION, STT_FILE, hn, hsec]

theorem readSym_undefEnt {shs : List Shdr} {strs : List UInt8} {nm : Nat} {n : String}
    (hnm : nm ≠ 0) (hn : strAt strs nm = some n) :
    readSym shs strs false (undefEnt nm) = some (.undef n) := by
  simp [readSym, undefEnt, Sym.bind, Sym.type, STB_GLOBAL, STT_NOTYPE, STT_SECTION, STT_FILE,
    STT_FUNC, hnm, hn]

theorem defSyms_global {i : Nat} (hi : i < (defSyms o).length) :
    (defSyms o)[i].global = decide ((locals o).length ≤ i) := by
  unfold defSyms at hi ⊢
  by_cases h : i < (locals o).length
  · rw [List.getElem_append_left h]
    have := (List.mem_filter.mp
      (show (locals o)[i] ∈ o.symbols.filter (!·.global) from List.getElem_mem h)).2
    simp only [Bool.not_eq_true'] at this
    rw [this]; simp; omega
  · have h' : i - (locals o).length < (globals o).length := by simp at hi; omega
    rw [List.getElem_append_right (by omega)]
    have := (List.mem_filter.mp (show (globals o)[i - (locals o).length] ∈
      o.symbols.filter (·.global) from List.getElem_mem h')).2
    rw [this]; simp; omega

theorem mem_defSyms {s : Symbol} : s ∈ defSyms o ↔ s ∈ o.symbols := by
  simp only [defSyms, locals, globals, List.mem_append, List.mem_filter]
  cases s.global <;> simp

/-- The symbol table reads back as the defined symbols and then the undefined names. -/
theorem readSyms_symEnts (g : Good m o) :
    readSyms (hdrs m o) (strtabBytes o) (locals o).length (symEnts o).tail =
      some ((defSyms o).map .defn ++ (undefs o).map .undef) := by
  have hlo : (symOffs o).length = (defSyms o).length + (undefs o).length := by
    simp [symOffs, symNames]
  apply readSyms_of _ _ _ _ _ (by simp [symEnts, hlo])
  intro i hi
  simp only [symEnts, List.tail_cons] at hi ⊢
  by_cases h : i < (defSyms o).length
  · have hA : i < (List.zipWith (symEnt o) (symOffs o) (defSyms o)).length := by simp; omega
    rw [List.getElem_append_left hA, List.getElem_zipWith,
      List.getElem_append_left (by simpa using h), List.getElem_map]
    have hg := defSyms_global h
    have hl : decide (i < (locals o).length) = !(defSyms o)[i].global := by
      rw [hg]; cases h : decide (i < (locals o).length) <;> simp_all
    rw [hl]
    apply readSym_symEnt g (mem_defSyms.mp (List.getElem_mem h)) (symOffs_pos _)
    rw [strAt_symOffs g]
    simp [symNames, List.getElem_append_left, h]
  · have hA : (List.zipWith (symEnt o) (symOffs o) (defSyms o)).length = (defSyms o).length := by
      simp; omega
    have hB : i - (defSyms o).length < (undefs o).length := by
      simp [hA] at hi; omega
    rw [List.getElem_append_right (by omega), List.getElem_zipWith,
      List.getElem_append_right (by simpa using h), List.getElem_map]
    have hl : decide (i < (locals o).length) = false := by
      have : (locals o).length ≤ (defSyms o).length := by simp [defSyms]
      simp; omega
    simp only [hA, List.getElem_drop]
    rw [hl]
    have hi' : (defSyms o).length + (i - (defSyms o).length) < (symOffs o).length := by omega
    apply readSym_undefEnt (symOffs_pos hi')
    rw [strAt_symOffs g]
    simp only [symNames]
    rw [List.getElem_append_right (by simp)]
    simp

/-! ### Reading the relocations -/

theorem readRelas_append (m : Mach) (bs : List UInt8) (shs : List Shdr) (rs : List RSym) :
    ∀ {A B : List Shdr} {a b : List Reloc}, readRelas m bs shs rs A = some a →
      readRelas m bs shs rs B = some b → readRelas m bs shs rs (A ++ B) = some (a ++ b)
  | [], _, a, _, ha, hb => by cases ha; simpa using hb
  | h :: A, B, a, b, ha, hb => by
    simp only [readRelas, List.cons_append] at ha ⊢
    split at ha
    · rename_i hc
      rw [ite_eq_left hc]
      split at ha
      · rename_i r rs' e1 e2
        cases ha
        rw [e1, readRelas_append m bs shs rs e2 hb]
        simp
      · cases ha
    · rename_i hc
      rw [ite_eq_right hc]
      exact readRelas_append m bs shs rs ha hb

theorem readRelas_none (m : Mach) (bs : List UInt8) (shs : List Shdr) (rs : List RSym) :
    ∀ l : List Shdr, (∀ h ∈ l, h.cls ≠ .rela) → readRelas m bs shs rs l = some []
  | [], _ => rfl
  | h :: l, hl => by
    simp only [readRelas, ite_eq_right (hl h (by simp))]
    exact readRelas_none m bs shs rs l (fun x hx => hl x (by simp [hx]))

theorem readRelas_of (m : Mach) (bs : List UInt8) (shs : List Shdr) (rs : List RSym) :
    ∀ (l : List Shdr) (gs : List (List Reloc)) (hl : l.length = gs.length),
    (∀ i (hi : i < l.length), l[i].cls = .rela ∧
      readRela m bs shs rs l[i] = some (gs[i]'(hl ▸ hi))) →
    readRelas m bs shs rs l = some gs.flatten
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl
  | h :: l, g :: gs, hl, H => by
    obtain ⟨h1, h2⟩ := H 0 (by simp)
    simp only [List.getElem_cons_zero] at h1 h2
    rw [readRelas, ite_eq_left h1, h2,
      readRelas_of m bs shs rs l gs (by simpa using hl) (fun i hi => H (i + 1) (by simpa using hi))]
    simp

/-- What the reader reads the symbol table as. -/
def rsymsOf (o : Obj) : List RSym := (defSyms o).map .defn ++ (undefs o).map .undef

theorem rsymsOf_name (o : Obj) (k : Nat) :
    ((rsymsOf o)[k]?).bind RSym.name? = (symNames o)[k]? := by
  have : (rsymsOf o).map RSym.name? = (symNames o).map some := by
    simp [rsymsOf, symNames, Function.comp_def, RSym.name?]
  have h := congrArg (·[k]?) this
  simp only [List.getElem?_map] at h
  cases e1 : (rsymsOf o)[k]? <;> cases e2 : (symNames o)[k]? <;> simp_all

theorem sym_mem_symNames {r : Reloc} (hr : r ∈ o.relocs) : r.sym ∈ symNames o := by
  simp only [symNames, List.mem_append, List.mem_map, undefs, mem_dedup, List.mem_filter]
  by_cases h : r.sym ∈ o.symbols.map (·.name)
  · obtain ⟨s, hs, e⟩ := List.mem_map.mp h
    exact .inl ⟨s, mem_defSyms.mpr hs, e⟩
  · exact .inr ⟨⟨r, hr, rfl⟩, by simpa using h⟩

theorem readRel_relaEnt (hm : m.Lawful) (g : Good m o) {r : Reloc} (hr : r ∈ o.relocs) :
    readRel m (rsymsOf o) r.sec (relaEnt m o r) = some r := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (g.kinds r hr)
  obtain ⟨hk, hlt⟩ := hm _ _ ht
  have hmem := sym_mem_symNames hr
  have hidx : (symNames o).idxOf r.sym < (symNames o).length := List.idxOf_lt_length_of_mem hmem
  have e1 : (symIdx o r.sym * 2 ^ 32 + t) % 2 ^ 32 = t := by omega
  have e2 : (symIdx o r.sym * 2 ^ 32 + t) / 2 ^ 32 = symIdx o r.sym := by omega
  have hn : ((rsymsOf o)[symIdx o r.sym - 1]?).bind RSym.name? = some r.sym := by
    rw [rsymsOf_name, symIdx, Nat.add_sub_cancel, List.getElem?_eq_getElem hidx,
      List.getElem_idxOf hidx]
  have h0 : symIdx o r.sym ≠ 0 := Nat.add_one_ne_zero _
  simp only [readRel, relaEnt, ht, Option.getD_some, e1, e2, hk, hn, h0, ite_false,
    signed64_addendBits (g.addend r hr).1 (g.addend r hr).2]

theorem readRels_of (m : Mach) (rs : List RSym) (sec : Nat) :
    ∀ g : List Reloc, (∀ r ∈ g, readRel m rs sec (f r) = some r) →
      readRels m rs sec (g.map f) = some g
  | [], _ => rfl
  | r :: g, h => by
    simp only [List.map_cons, readRels, h r (by simp),
      readRels_of m rs sec g (fun x hx => h x (by simp [hx]))]

theorem symtab_hdr (g : Good m o) :
    ((hdrs m o)[o.sections.length + 2]?).map Shdr.type = some SHT_SYMTAB := by
  obtain ⟨nm, off, e1, -⟩ := fixAt g (k := 1) (x := symOut o) (by decide) (by simp [fixedOuts])
  rw [show o.sections.length + 2 = o.sections.length + 1 + 1 from rfl, e1]
  rfl

theorem readRela_relaOut (hm : m.Lawful) (g : Good m o) {p : Nat × List Reloc}
    (hp : p ∈ runs o.relocs) {nm off : Nat}
    (hc : contents (fileBytes m o) ((relaOut m o p).hdr nm off) = some (relaOut m o p).bytes) :
    readRela m (fileBytes m o) (hdrs m o) (rsymsOf o) ((relaOut m o p).hdr nm off) = some p.2 := by
  have hsec : ∀ r ∈ p.2, r.sec = p.1 := runs_sec _ p hp
  have hlt : p.1 < o.sections.length := by
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ (runs_ne_nil _ p hp)
    rw [← hsec r hr]
    exact g.rsec r (mem_of_mem_runs hp hr)
  have ht : table (fileBytes m o) relaW ((relaOut m o p).hdr nm off) =
      some (p.2.map (relaEnt m o)) := by
    apply table_of_contents hc rfl (by decide)
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    exact fun r hr => g.relas r (mem_of_mem_runs hp hr)
  unfold readRela
  rw [ite_eq_left ⟨.inr rfl, symtab_hdr g⟩]
  simp only [Out.hdr]
  simp only [relaOut] at ht ⊢
  rw [secIdx_hdrs hlt]
  simp only [Out.hdr] at ht
  rw [ht]
  apply readRels_of
  intro r hr
  rw [← hsec r hr]
  exact readRel_relaEnt hm g (mem_of_mem_runs hp hr)

theorem readRelas_hdrs (hm : m.Lawful) (g : Good m o) :
    readRelas m (fileBytes m o) (hdrs m o) (rsymsOf o) (hdrs m o) = some o.relocs := by
  have h1 : readRelas m (fileBytes m o) (hdrs m o) (rsymsOf o)
      (Shdr.null :: (secHdrs m o ++ fixHdrs m o)) = some [] := by
    apply readRelas_none
    intro h hh
    simp only [List.mem_cons, List.mem_append] at hh
    rcases hh with rfl | hh | hh
    · simp
    · obtain ⟨k, hk⟩ := secHdrs_cls hh; simp [hk]
    · rcases fixHdrs_cls hh with e | e | e <;> simp [e]
  have h2 : readRelas m (fileBytes m o) (hdrs m o) (rsymsOf o) (relHdrs m o) =
      some (((runs o.relocs).map (·.2)).flatten) := by
    apply readRelas_of _ _ _ _ _ _ (by simp)
    intro j hj
    have hj' : j < (runs o.relocs).length := by simpa using hj
    obtain ⟨nm, off, e1, -, e3⟩ := hdrAt g (outs_rela (m := m) (o := o) hj')
    have e : (relHdrs m o)[j] = (relaOut m o (runs o.relocs)[j]).hdr nm off := by
      have := relHdrs_get (m := m) (o := o) j
      rw [e1, List.getElem?_eq_getElem hj] at this
      exact Option.some.inj this
    rw [e]
    refine ⟨by simp [relaOut_cls], ?_⟩
    simp only [List.getElem_map]
    exact readRela_relaOut hm g (List.getElem_mem hj') (e3 rfl)
  have := readRelas_append _ _ _ _ h1 h2
  rw [runs_flatten] at this
  simpa [hdrs_eq, allHdrs_split] using this

/-! ### The round trip -/

theorem decode_hdrs (g : Good m o) :
    (decodeTab shdrW (ehdr m o).shnum ((fileBytes m o).drop (ehdr m o).shoff)).map Shdr.ofList =
      hdrs m o := by
  have e : fileBytes m o = (Elf.encodeEhdr (ehdr m o) ++ lay 64 (outs m o) ++
      zeros (shoff m o - layEnd 64 (outs m o))) ++ encodeTab shdrW ((hdrs m o).map Shdr.toList) := by
    simp [fileBytes]
  have hn : (ehdr m o).shnum = ((hdrs m o).map Shdr.toList).length := by
    simp [ehdr, hdrs_eq]
  rw [e, hn, show (ehdr m o).shoff = shoff m o from rfl, List.drop_left' prefix_length,
    ← List.append_nil (encodeTab shdrW _), decodeTab_encodeTab _ _ (hdrs_fit g)]
  simp [Function.comp_def]

theorem namesOk_rsymsOf : namesOk (rsymsOf o) = true := by
  have h1 : (rsymsOf o).filterMap RSym.undef? = undefs o := by
    simp [rsymsOf, List.filterMap_append, Function.comp_def, RSym.undef?]
  have h2 : (rsymsOf o).filterMap RSym.sym? = defSyms o := by
    simp [rsymsOf, List.filterMap_append, Function.comp_def, RSym.sym?]
  simp only [namesOk, h1, h2, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]
  intro n hn hd
  simp only [undefs, mem_dedup, List.mem_filter, List.contains_eq_mem, Bool.not_eq_true',
    decide_eq_false_iff_not] at hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hd
  exact hn.2 (List.mem_map.mpr ⟨s, mem_defSyms.mp hs, rfl⟩)

theorem symEnts_length : (symEnts o).length = (defSyms o).length + (undefs o).length + 1 := by
  have hlo : (symOffs o).length = (defSyms o).length + (undefs o).length := by
    simp [symOffs, symNames]
  simp [symEnts, hlo]

theorem read_write_aux (hm : m.Lawful) (g : Good m o) :
    read m (fileBytes m o) = some { o with symbols := defSyms o } := by
  have hdec : Elf.decodeEhdr (fileBytes m o) = some (ehdr m o) := by
    rw [fileBytes, List.append_assoc, List.append_assoc]
    exact Elf.decodeEhdr_encodeEhdr _ g.ehdr _
  have hok : ehdrOk m (ehdr m o) (fileBytes m o).length = true := by
    have := g.shnum
    simp [ehdrOk, ehdr, fileBytes_length g, ET_REL, Elf.EV_CURRENT, Elf.EHDR_SIZE, SHDR_SIZE]
    exact decide_eq_true (by simpa [SHN_LORESERVE] using this)
  have hbad : (hdrs m o).all (·.cls != .bad) = true := by
    simp only [List.all_eq_true, bne_iff_ne, ne_eq]
    intro h hh
    rw [hdrs_eq, allHdrs_split] at hh
    simp only [List.mem_cons, List.mem_append] at hh
    rcases hh with rfl | hh | hh | hh
    · simp
    · obtain ⟨k, hk⟩ := secHdrs_cls hh; simp [hk]
    · rcases fixHdrs_cls hh with e | e | e <;> simp [e]
    · simp [relHdrs_cls hh]
  obtain ⟨nm, off, hf, hc⟩ := symtab_filter g
  have htab : table (fileBytes m o) symW ((symOut o).hdr nm off) =
      some ((symEnts o).map Sym.toList) := by
    apply table_of_contents hc rfl (by decide)
    simpa using g.syms
  have hsyms := readSyms_symEnts g
  have hsl := symEnts_length (o := o)
  unfold read
  rw [hdec]
  simp only [hok, ite_true, decode_hdrs g]
  rw [ite_eq_left ⟨by simp [hdrs_eq], hbad⟩,
    show (ehdr m o).shstrndx = o.sections.length + 4 from rfl, strSec_shstrtab g]
  simp only [loadSecs_hdrs g]
  unfold readRest
  rw [hf]
  simp only [Out.hdr, symOut] at htab ⊢
  rw [strSec_strtab g, htab]
  cases e : symEnts o with
  | nil => simp [symEnts] at e
  | cons e0 es =>
    have h0 : e0 = Sym.null := by simp only [symEnts] at e; exact (List.cons.inj e).1.symm
    subst h0
    rw [e] at hsyms hsl
    simp only [List.tail_cons] at hsyms
    simp only [List.map_cons, List.length_map, List.length_cons] at hsl ⊢
    have hlo : (locals o).length ≤ (defSyms o).length := by simp [defSyms]
    rw [show (defSyms o).map .defn ++ (undefs o).map .undef = rsymsOf o from rfl] at hsyms
    rw [ite_eq_left ⟨by simp [symtabOk]; omega, rfl⟩]
    simp only [List.map_map, Function.comp_def, Sym.ofList_toList, List.map_id', Nat.add_sub_cancel,
      hsyms, namesOk_rsymsOf, ite_true, readRelas_hdrs hm g, Option.map_some]
    simp [rsymsOf, List.filterMap_append, Function.comp_def, RSym.sym?]

/-- An object with its local symbols before its global ones, which is the order of an ELF symbol
table. -/
def _root_.Millipede.Obj.norm (o : Obj) : Obj := { o with symbols := defSyms o }

/-- The reader gives back every object the writer accepts, with its local symbols first. -/
theorem read_write (hm : m.Lawful) {bs : List UInt8} (h : write m o = .ok bs) :
    read m bs = some o.norm := by
  obtain ⟨g, rfl⟩ := good_of_write h
  exact read_write_aux hm g

/-! ### Linking objects read back -/

theorem eq_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup →
    ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: l, hn, a, b, ha, hb, he => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd he.symm (hn.1 b hb)
    · exact absurd he (hn.1 a ha)
    · exact eq_of_nodup_map hn.2 ha hb he

/-- `find?` gives the same answer on a permutation when at most one element satisfies the
predicate. -/
theorem find?_perm {α : Type} {p : α → Bool} {l l' : List α} (h : l.Perm l')
    (hu : ∀ a ∈ l, ∀ b ∈ l, p a = true → p b = true → a = b) : l.find? p = l'.find? p := by
  cases h1 : l.find? p with
  | none =>
    rw [List.find?_eq_none] at h1
    rw [eq_comm, List.find?_eq_none]
    exact fun x hx => h1 x (h.mem_iff.mpr hx)
  | some a =>
    have ha := h.mem_iff.mp (List.mem_of_find?_eq_some h1)
    have hpa := List.find?_some h1
    cases h2 : l'.find? p with
    | none => exact absurd hpa (List.find?_eq_none.mp h2 a ha)
    | some b =>
      have hb := h.mem_iff.mpr (List.mem_of_find?_eq_some h2)
      rw [hu a (List.mem_of_find?_eq_some h1) b hb hpa (List.find?_some h2)]

theorem defSyms_perm (o : Obj) : (defSyms o).Perm o.symbols := by
  unfold defSyms locals globals
  exact List.perm_append_comm.trans (List.filter_append_perm _ _)

/-- With unique names, looking a symbol up in the reordered list finds the same symbol. -/
theorem find?_defSyms {o : Obj} (hn : (o.symbols.map (·.name)).Nodup) {p : Symbol → Bool}
    (hp : ∀ a b, p a = true → p b = true → a.name = b.name) :
    (defSyms o).find? p = o.symbols.find? p :=
  (find?_perm (defSyms_perm o).symm (fun a ha b hb pa pb =>
    eq_of_nodup_map hn ha hb (hp a b pa pb))).symm

theorem globals_defSyms (o : Obj) : (defSyms o).filter (·.global) = o.symbols.filter (·.global) := by
  simp only [defSyms, locals, globals, List.filter_append, List.filter_filter]
  rw [List.filter_eq_nil_iff.mpr (by intro a ha; simp at ha ⊢)]
  simp

theorem items_norm : ∀ (j : Nat) (objs : List Obj), Link.items j (objs.map Obj.norm) = Link.items j objs
  | _, [] => rfl
  | j, o :: os => by simp [Link.items, Obj.norm, items_norm (j + 1) os]

theorem layout_norm (cfg : Link.Config) (objs : List Obj) :
    Link.layout cfg (objs.map Obj.norm) = Link.layout cfg objs := by
  simp [Link.layout, Link.groupItems, items_norm]

theorem globalNames_norm (objs : List Obj) :
    Link.globalNames (objs.map Obj.norm) = Link.globalNames objs := by
  rw [Link.globalNames, Link.globalNames, List.flatMap_map]
  congr 1; funext o
  simp only [Obj.norm, globals_defSyms]

theorem globalSym_norm (n : String) : ∀ (j : Nat) (objs : List Obj),
    Link.globalSym n j (objs.map Obj.norm) = Link.globalSym n j objs
  | _, [] => rfl
  | j, o :: os => by
    have : (defSyms o).find? (fun s => s.global && s.name == n) =
        o.symbols.find? (fun s => s.global && s.name == n) := by
      have := congrArg (List.find? (fun s => s.name == n)) (globals_defSyms o)
      simp only [List.find?_filter] at this
      exact this
    simp only [List.map_cons, Link.globalSym, Obj.norm, this, globalSym_norm n (j + 1) os]

theorem globalAddr_norm (L : Link.Layout) (objs : List Obj) (n : String) :
    Link.globalAddr L (objs.map Obj.norm) n = Link.globalAddr L objs n := by
  simp only [Link.globalAddr, globalSym_norm]

theorem resolve_norm (L : Link.Layout) {objs : List Obj}
    (hn : ∀ o ∈ objs, (o.symbols.map (·.name)).Nodup) (j : Nat) :
    Link.resolve L (objs.map Obj.norm) j = Link.resolve L objs j := by
  funext n
  unfold Link.resolve
  rw [globalAddr_norm]
  cases h : objs[j]? with
  | none => simp only [List.getElem?_map, h, Option.map_none, Option.bind_none]
  | some o =>
    have hf : (defSyms o).find? (fun s => s.name == n) = o.symbols.find? (fun s => s.name == n) :=
      find?_defSyms (hn o (List.mem_of_getElem? h)) (by
        intro a b ha hb; simp only [beq_iff_eq] at ha hb; rw [ha, hb])
    simp only [List.getElem?_map, h, Option.map_some, Option.bind_some, Obj.norm, hf]

theorem allRelocsOk_norm (L : Link.Layout) {objs : List Obj}
    (hr : ∀ j, Link.resolve L (objs.map Obj.norm) j = Link.resolve L objs j) :
    ∀ (j : Nat) (os : List Obj),
      Link.allRelocsOk L (objs.map Obj.norm) j (os.map Obj.norm) = Link.allRelocsOk L objs j os
  | _, [] => rfl
  | j, o :: os => by
    simp only [List.map_cons, Link.allRelocsOk, allRelocsOk_norm L hr (j + 1) os, Link.relocsOk,
      Obj.norm, hr]

theorem content_norm (L : Link.Layout) {objs : List Obj}
    (hr : ∀ j, Link.resolve L (objs.map Obj.norm) j = Link.resolve L objs j) :
    Link.content L (objs.map Obj.norm) = Link.content L objs := by
  funext it a
  simp only [Link.content, hr]

theorem nodup_norm (o : Obj) :
    ((o.norm.symbols.map (·.name)).Nodup) ↔ (o.symbols.map (·.name)).Nodup :=
  ((defSyms_perm o).map _).nodup_iff

/-- The order of each object's symbols does not change what `link` does. -/
theorem link_norm (cfg : Link.Config) (objs : List Obj) :
    Link.link cfg (objs.map Obj.norm) = Link.link cfg objs := by
  have hall : ((objs.map Obj.norm).all fun o => decide (o.symbols.map (·.name)).Nodup) =
      objs.all fun o => decide (o.symbols.map (·.name)).Nodup := by
    simp only [List.all_map, Function.comp_def, nodup_norm]
  have hsec : ((objs.map Obj.norm).all fun o => o.symbols.all (·.sec < o.sections.length)) =
      objs.all fun o => o.symbols.all (·.sec < o.sections.length) := by
    simp only [List.all_map, Function.comp_def]
    congr 1; funext o
    show (defSyms o).all _ = o.symbols.all _
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun h s hs => h s (mem_defSyms.mpr hs), fun h s hs => h s (mem_defSyms.mp hs)⟩
  have hg : ∀ g, Link.groupItems g (objs.map Obj.norm) = Link.groupItems g objs := by
    intro g; simp [Link.groupItems, items_norm]
  unfold Link.link
  rw [hall, hsec, globalNames_norm, layout_norm]
  by_cases hn : (objs.all fun o => decide ((o.symbols.map (·.name)).Nodup)) = true
  · have hn' : ∀ o ∈ objs, (o.symbols.map (·.name)).Nodup := by simpa using hn
    have hr := resolve_norm (Link.layout cfg objs) hn'
    simp only [allRelocsOk_norm _ hr, content_norm _ hr, hg, globalAddr_norm]
  · simp only [Bool.not_eq_true] at hn
    simp only [hn, Link.req, Bool.false_eq_true, ite_false]
    rfl

theorem mapM_read_write (hm : m.Lawful) : ∀ {objs : List Obj} {files : List (List UInt8)},
    objs.mapM (write m) = .ok files → files.mapM (read m) = some (objs.map Obj.norm)
  | [], files, h => by cases h; rfl
  | o :: os, files, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hw : write m o with
    | error e => rw [hw] at h; cases h
    | ok bs =>
      rw [hw] at h
      cases hr : os.mapM (write m) with
      | error e => rw [hr] at h; cases h
      | ok bss =>
        rw [hr] at h
        cases h
        simp [List.mapM_cons, read_write hm hw, mapM_read_write hm hr]

/-- Linking the objects read back from written files is linking the original objects: the files
read back as the objects with their local symbols first, and that order does not change `link`. -/
theorem link_read_write (hm : m.Lawful) (cfg : Link.Config) {objs : List Obj}
    {files : List (List UInt8)} (h : objs.mapM (write m) = .ok files) :
    (files.mapM (read m)).map (Link.link cfg) = some (Link.link cfg objs) := by
  rw [mapM_read_write hm h, Option.map_some, link_norm]

end

end Millipede.ElfRel
