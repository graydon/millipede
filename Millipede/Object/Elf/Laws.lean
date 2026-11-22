import Millipede.Object.Elf.Write
import Millipede.Object.Elf.Load
import Millipede.Object.Format

/-!
# Laws of the ELF64 format

The main law is `parse_write`, which says that the loader reads back exactly the image the writer
was given, so `write img = .ok bs` implies `parse bs = some img`. From it follows `load_write`,
which says that loading the written bytes gives the image's initial machine state. `write_valid`
says that the writer accepts only valid images, and `write_ok` that it accepts every image that is
valid for the platform and whose header fields fit. `parse_disjoint` and `load_disjoint` say that
the segments of any file the loader accepts lie in address order on pairwise disjoint pages, and
`load_wxorx` that the loaded memory is W^X.

`Elf.format c abi` is the `Format isa abi` value and `Elf.laws` proves its `Format.Laws`.
`Elf.x64Linux abi` is the instance for x86-64 Linux, and `Elf.a64Linux abi` the one for AArch64
Linux.
-/

namespace Millipede.Elf

/-! ### Segments round-trip -/

theorem all_zeros (n : Nat) : (zeros n).all (· == 0) = true := by
  simp [zeros, List.all_replicate]

theorem pad_add {P : Nat} (hP : 0 < P) (l : Nat) : l + pad P l = chunkLen P l := by
  have := le_chunkLen hP l
  unfold pad; omega

/-- A segment's `PT_LOAD` header, read against a file that holds the segment's padded bytes at its
offset, gives back the segment. -/
theorem loadSeg_segPhdr {P : Nat} (pre rest : List UInt8) (sg : Segment)
    (hoff : pre.length % P = 0) (hle : sg.bytes.length ≤ sg.memSize) :
    loadSeg P (pre ++ (sg.bytes ++ (zeros (pad P sg.bytes.length) ++ rest)))
      (segPhdr P pre.length sg) = some sg := by
  have e1 : pre ++ (sg.bytes ++ (zeros (pad P sg.bytes.length) ++ rest)) =
      (pre ++ sg.bytes) ++ (zeros (pad P sg.bytes.length) ++ rest) := by simp
  have hl : (pre ++ sg.bytes).length = pre.length + sg.bytes.length := by simp
  have hz : (zeros (pad P sg.bytes.length)).length = pad P sg.bytes.length := by simp
  have hz' : ((List.drop (pre.length + sg.bytes.length)
      (pre ++ (sg.bytes ++ (zeros (pad P sg.bytes.length) ++ rest)))).take
        (pad P sg.bytes.length)).all (· == 0) = true := by
    rw [e1, List.drop_left' hl, List.take_left' hz]
    exact all_zeros _
  unfold loadSeg
  rw [ite_eq_left ⟨permFlags_lt _, hoff, rfl, hle, by simp [segPhdr], hz'⟩]
  simp only [segPhdr, List.drop_left' rfl, List.take_left' rfl, UInt64.ofNat_toNat,
    flagsPerm_permFlags]

/-- The program headers that `layout` produces, read against a file that holds `blob` at their
offset, give back the segments. -/
theorem loadSegs_layout {P : Nat} (hP : 0 < P) : ∀ (segs : List Segment) (pre : List UInt8),
    pre.length % P = 0 → segs.all (fun sg => decide (sg.bytes.length ≤ sg.memSize)) = true →
    loadSegs P (pre ++ blob P segs) (layout P pre.length segs) = some segs
  | [], _, _, _ => rfl
  | sg :: sgs, pre, hoff, hle => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hle
    have e : pre ++ blob P (sg :: sgs) =
        (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length))) ++ blob P sgs := by
      simp [blob]
    have hl : (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length))).length =
        pre.length + chunkLen P sg.bytes.length := by
      simp [List.length_append, ← pad_add hP sg.bytes.length]
    have hoff' : (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length))).length % P = 0 := by
      rw [hl, Nat.add_mod, hoff, chunkLen_mod, Nat.zero_mod]
    have ih := loadSegs_layout hP sgs _ hoff' hle.2
    rw [hl, ← e] at ih
    have h1 : loadSeg P (pre ++ blob P (sg :: sgs)) (segPhdr P pre.length sg) = some sg := by
      have := loadSeg_segPhdr pre (blob P sgs) sg hoff hle.1
      simpa [blob] using this
    simp only [layout, loadSegs, h1, ih]

/-- `splitPhdrs` finds the loads and the stack header that the writer emitted. -/
theorem splitPhdrs_layout (P : Nat) (st : Phdr) (hst : st.type = PT_GNU_STACK) :
    ∀ (off : Nat) (segs : List Segment),
    splitPhdrs (layout P off segs ++ [st]) = some (layout P off segs, st)
  | _, [] => by
    simp [layout, splitPhdrs, hst, PT_GNU_STACK, PT_LOAD]
  | off, sg :: sgs => by
    simp only [layout, List.cons_append, splitPhdrs, segPhdr, ite_true,
      splitPhdrs_layout P st hst _ sgs, Option.map_some]

@[simp] theorem layout_length (P : Nat) : ∀ (off : Nat) (segs : List Segment),
    (layout P off segs).length = segs.length
  | _, [] => rfl
  | _, _ :: sgs => by simp [layout, layout_length P _ sgs]

/-! ### Facts from the image check -/

theorem imageOk_valid {c : Config} {pageBits : Nat} {stackTop : UInt64} {img : Image}
    (h : imageOk c pageBits stackTop img = true) : validAt pageBits stackTop img = true := by
  simp only [imageOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.2

theorem validAt_bytes_le {pageBits : Nat} {stackTop : UInt64} {img : Image}
    (h : validAt pageBits stackTop img = true) :
    img.segments.all (fun sg => decide (sg.bytes.length ≤ sg.memSize)) = true := by
  simp only [validAt, Bool.and_eq_true, List.all_eq_true] at h
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro sg hm
  have := h.1.2 sg hm
  simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1.2

/-! ### The round trip -/

/-- How `parse` succeeds, step by step. -/
theorem parse_of {c : Config} {pageBits : Nat} {stackTop : UInt64} {bs : List UInt8}
    {h : Ehdr} {loads : List Phdr} {st : Phdr} {segs : List Segment}
    (h1 : decodeEhdr bs = some h) (h2 : ehdrOk c h bs.length = true)
    (h3 : splitPhdrs (decodePhdrs h.phnum (bs.drop h.phoff)) = some (loads, st))
    (h4 : st.flags = PF_R + PF_W) (h5 : loadSegs (2 ^ pageBits) bs loads = some segs)
    (h6 : imageOk c pageBits stackTop
      { segments := segs, entry := UInt64.ofNat h.entry, stackSize := st.memsz } = true) :
    parse c pageBits stackTop bs =
      some { segments := segs, entry := UInt64.ofNat h.entry, stackSize := st.memsz } := by
  simp [parse, h1, h2, h3, h4, h5, h6]

/-- `write` succeeds only on a checked image whose headers fit, and then returns `fileBytes`. -/
theorem write_inv {c : Config} {pageBits : Nat} {stackTop : UInt64} {img : Image}
    {bs : List UInt8} (h : write c pageBits stackTop img = .ok bs) :
    imageOk c pageBits stackTop img = true ∧
      (ehdrOf c img (phdrsOf (2 ^ pageBits) img).length).fits = true ∧
      (phdrsOf (2 ^ pageBits) img).all Phdr.fits = true ∧
      bs = fileBytes c (2 ^ pageBits) img := by
  unfold write at h; grind

/-- The loader model parses what the writer wrote into exactly the image the writer was given. -/
theorem parse_write {c : Config} {pageBits : Nat} {stackTop : UInt64} {img : Image}
    {bs : List UInt8} (h : write c pageBits stackTop img = .ok bs) :
    parse c pageBits stackTop bs = some img := by
  have hP : 0 < 2 ^ pageBits := Nat.two_pow_pos _
  obtain ⟨hok', hfe, hfp, hbs⟩ := write_inv h
  let P := 2 ^ pageBits
  let phs := phdrsOf P img
  let eh := ehdrOf c img phs.length
  let gap := zeros (dataStart P img - headerSize phs.length)
  have hn : phs.length = img.segments.length + 1 := by simp [phs, phdrsOf]
  have hhs : headerSize phs.length ≤ dataStart P img := by
    rw [hn]; exact le_chunkLen hP _
  have hfile : fileBytes c P img =
      encodeEhdr eh ++ (encodePhdrs phs ++ (gap ++ blob P img.segments)) := by
    simp [fileBytes, eh, phs, gap]
  have hpre : (encodeEhdr eh ++ (encodePhdrs phs ++ gap)).length = dataStart P img := by
    simp [gap, headerSize, EHDR_SIZE] at hhs ⊢; omega
  have hsegs := loadSegs_layout hP img.segments _ (by rw [hpre]; exact chunkLen_mod _ _)
    (validAt_bytes_le (imageOk_valid hok'))
  rw [hpre] at hsegs
  simp only [List.append_assoc] at hsegs
  have e : Image.mk img.segments (UInt64.ofNat eh.entry) (stackPhdr img.stackSize).memsz =
      img := by
    simp [eh, ehdrOf, stackPhdr]
  have hparse := parse_of (c := c) (pageBits := pageBits) (stackTop := stackTop)
    (bs := encodeEhdr eh ++ (encodePhdrs phs ++ (gap ++ blob P img.segments)))
    (h := eh) (loads := layout P (dataStart P img) img.segments)
    (st := stackPhdr img.stackSize) (segs := img.segments)
    (decodeEhdr_encodeEhdr _ hfe _)
    (by
      simp only [ehdrOk, eh, ehdrOf, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
      simp [gap, headerSize, EHDR_SIZE] at hhs ⊢)
    (by
      rw [show eh.phoff = (encodeEhdr eh).length by simp [eh, ehdrOf], List.drop_left' rfl,
        show eh.phnum = phs.length from rfl, decodePhdrs_encodePhdrs phs hfp]
      exact splitPhdrs_layout _ _ rfl _ _)
    rfl hsegs
    (by rw [e]; exact hok')
  rw [e] at hparse
  rw [hbs, hfile]; exact hparse

/-- Loading what the ELF writer produced gives exactly the image's initial machine state. -/
theorem load_write {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    (h : write c abi.pageBits abi.stackTop img = .ok bs) : load c abi bs = some (img.init abi) := by
  simp [load, parse_write h]

/-- The writer only accepts images that pass `imageOk`. -/
theorem write_imageOk {c : Config} {pageBits : Nat} {stackTop : UInt64} {img : Image}
    {bs : List UInt8} (h : write c pageBits stackTop img = .ok bs) :
    imageOk c pageBits stackTop img = true := by
  unfold write at h
  simp only at h
  split at h
  · cases h
  · rename_i hok; simpa using hok

/-- The writer refuses invalid images. -/
theorem write_valid {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    (h : write c abi.pageBits abi.stackTop img = .ok bs) : img.valid abi = true := by
  rw [valid_eq]; exact imageOk_valid (write_imageOk h)

/-! ### The `Format` value -/

/-- The static ELF64 format for an ABI, under the OS facts `c`. -/
def format (c : Config) {isa : Isa} (abi : Abi isa) : Format isa abi where
  write := write c abi.pageBits abi.stackTop
  load := load c abi

/-- The ELF format satisfies the format laws. -/
theorem laws (c : Config) {isa : Isa} (abi : Abi isa) : (format c abi).Laws where
  write_valid _ _ h := write_valid h
  load_write _ _ h := load_write h

/-- Static ELF64 for x86-64 Linux. -/
def x64Linux {isa : Isa} (abi : Abi isa) : Format isa abi := format Config.x64Linux abi

theorem x64Linux_laws {isa : Isa} (abi : Abi isa) : (x64Linux abi).Laws := laws _ abi

/-- Static ELF64 for AArch64 Linux. -/
def a64Linux {isa : Isa} (abi : Abi isa) : Format isa abi := format Config.a64Linux abi

theorem a64Linux_laws {isa : Isa} (abi : Abi isa) : (a64Linux abi).Laws := laws _ abi

/-! ### Accepted files: segments are disjoint, memory is W^X -/

/-- Whatever the loader model accepts passes the image check. -/
theorem parse_imageOk {c : Config} {pageBits : Nat} {stackTop : UInt64} {bs : List UInt8}
    {img : Image} (h : parse c pageBits stackTop bs = some img) :
    imageOk c pageBits stackTop img = true := by
  unfold parse at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · dsimp only at h
          split at h
          · cases h; assumption
          · cases h
      · cases h
  · cases h

theorem firstPage_le_lastPage (pb : Nat) (sg : Segment) (h : 0 < sg.memSize) :
    sg.firstPage pb ≤ sg.lastPage pb :=
  Nat.div_le_div_right (by omega)

/-- In a sorted, disjoint list of non-empty segments, the head ends before every later one
starts. -/
theorem sortedDisjoint_head (pb : Nat) : ∀ (a : Segment) (l : List Segment),
    Image.sortedDisjoint pb (a :: l) = true → (∀ s ∈ l, 0 < s.memSize) →
    ∀ x ∈ l, a.lastPage pb < x.firstPage pb
  | _, [], _, _, x, hx => by cases hx
  | a, b :: rest, h, hpos, x, hx => by
    simp only [Image.sortedDisjoint, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · have := sortedDisjoint_head pb b rest h.2 (fun s hs => hpos s (List.mem_cons_of_mem _ hs))
        x hx
      have := firstPage_le_lastPage pb b (hpos b List.mem_cons_self)
      omega

/-- Sorted disjoint non-empty segments are pairwise on disjoint page ranges, in address
order. -/
theorem sortedDisjoint_pairwise (pb : Nat) : ∀ (l : List Segment),
    Image.sortedDisjoint pb l = true → (∀ s ∈ l, 0 < s.memSize) →
    l.Pairwise (fun a b => a.lastPage pb < b.firstPage pb)
  | [], _, _ => List.Pairwise.nil
  | a :: l, h, hpos => by
    refine List.Pairwise.cons (sortedDisjoint_head pb a l h
      (fun s hs => hpos s (List.mem_cons_of_mem _ hs))) ?_
    refine sortedDisjoint_pairwise pb l ?_ (fun s hs => hpos s (List.mem_cons_of_mem _ hs))
    cases l with
    | nil => rfl
    | cons b rest =>
      simp only [Image.sortedDisjoint, Bool.and_eq_true] at h
      exact h.2

/-- In any image that the loader model accepts, no page is touched by two different segments, and
the segments are in increasing address order. -/
theorem parse_disjoint {c : Config} {pageBits : Nat} {stackTop : UInt64} {bs : List UInt8}
    {img : Image} (h : parse c pageBits stackTop bs = some img) :
    img.segments.Pairwise (fun a b => a.lastPage pageBits < b.firstPage pageBits ∧
      ∀ p, ¬ (a.coversPage pageBits p = true ∧ b.coversPage pageBits p = true)) := by
  have hv := imageOk_valid (parse_imageOk h)
  simp only [validAt, Bool.and_eq_true, List.all_eq_true] at hv
  have hpos : ∀ s ∈ img.segments, 0 < s.memSize := by
    intro s hs
    have := hv.1.2 s hs
    simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1
  refine (sortedDisjoint_pairwise pageBits _ hv.2 hpos).imp ?_
  intro a b hab
  refine ⟨hab, fun p ⟨ha, hb⟩ => ?_⟩
  simp only [Segment.coversPage, Bool.and_eq_true, decide_eq_true_eq] at ha hb
  omega

/-- The machine state that the loader model produces is the initial state of a valid image whose
segments lie on pairwise disjoint pages. -/
theorem load_disjoint {c : Config} {isa : Isa} {abi : Abi isa} {bs : List UInt8}
    {s : MState isa.Regs} (h : load c abi bs = some s) :
    ∃ img : Image, s = img.init abi ∧ img.valid abi = true ∧
      img.segments.Pairwise (fun a b => a.lastPage abi.pageBits < b.firstPage abi.pageBits ∧
        ∀ p, ¬ (a.coversPage abi.pageBits p = true ∧ b.coversPage abi.pageBits p = true)) := by
  unfold load at h
  cases hp : parse c abi.pageBits abi.stackTop bs with
  | none => rw [hp] at h; cases h
  | some img =>
    rw [hp] at h; cases h
    exact ⟨img, rfl, by rw [valid_eq]; exact imageOk_valid (parse_imageOk hp),
      parse_disjoint hp⟩

/-- Any file the loader model accepts starts in W^X memory. -/
theorem load_wxorx {c : Config} {isa : Isa} {abi : Abi isa} {bs : List UInt8}
    {s : MState isa.Regs} (h : load c abi bs = some s) : s.mem.WxorX := by
  obtain ⟨img, rfl, hv, _⟩ := load_disjoint h
  exact Image.init_wxorx abi img hv

/-! ### Completeness of the writer -/

@[simp] theorem blob_length {P : Nat} (hP : 0 < P) : ∀ segs : List Segment,
    (blob P segs).length = (segs.map (fun sg => chunkLen P sg.bytes.length)).sum
  | [] => rfl
  | sg :: sgs => by
    simp [blob, blob_length hP sgs, ← pad_add hP sg.bytes.length, Nat.add_assoc]

theorem layout_fits {P : Nat} (hP : 0 < P) (hP64 : P < 2 ^ 64) : ∀ (off : Nat)
    (segs : List Segment), (∀ sg ∈ segs, sg.memSize < 2 ^ 64) →
    off + (blob P segs).length < 2 ^ 64 → (layout P off segs).all Phdr.fits = true
  | _, [], _, _ => rfl
  | off, sg :: sgs, hm, hl => by
    have hc := pad_add hP sg.bytes.length
    simp only [blob_length hP, List.map_cons, List.sum_cons] at hl
    simp only [layout, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, layout_fits hP hP64 _ sgs (fun s hs => hm s (List.mem_cons_of_mem _ hs)) ?_⟩
    · have := hm sg List.mem_cons_self
      have := permFlags_lt sg.perm
      have := sg.vaddr.toNat_lt
      have := le_chunkLen hP sg.bytes.length
      simp only [Phdr.fits, Bool.and_eq_true, fits_iff]
      simp only [segPhdr, PT_LOAD, Nat.reducePow]
      omega
    · simp only [blob_length hP]; omega

/-- The writer is complete. It writes every image that passes the platform check, provided the
header fields can hold it, which needs the machine number, fewer than 65535 segments, a page size
and a stack limit below 2⁶⁴, and a file smaller than 2⁶⁴ bytes. -/
theorem write_ok {c : Config} {pageBits : Nat} {stackTop : UInt64} {img : Image}
    (hok : imageOk c pageBits stackTop img = true) (hm : c.machine < 2 ^ 16)
    (hpb : pageBits < 64) (hn : img.segments.length + 1 < 2 ^ 16) (hst : c.maxStack < 2 ^ 64)
    (hsz : (fileBytes c (2 ^ pageBits) img).length < 2 ^ 64) :
    write c pageBits stackTop img = .ok (fileBytes c (2 ^ pageBits) img) := by
  have hP : 0 < 2 ^ pageBits := Nat.two_pow_pos _
  have hP64 : 2 ^ pageBits < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hpb
  have hok' := hok
  simp only [imageOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨_, hv⟩, _⟩, hss⟩, _⟩, _⟩ := hok'
  -- every segment's memory size is below 2^64, because the segment ends below the stack
  have hmem : ∀ sg ∈ img.segments, sg.memSize < 2 ^ 64 := by
    intro sg hs
    simp only [validAt, Bool.and_eq_true, List.all_eq_true] at hv
    have h1 := hv.1.2 sg hs
    simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq] at h1
    have h2 : (stackTop.toNat / 2 ^ pageBits - img.stackPages pageBits) * 2 ^ pageBits ≤
        stackTop.toNat :=
      Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.div_mul_le_self _ _)
    have := stackTop.toNat_lt
    omega
  have hn' : (phdrsOf (2 ^ pageBits) img).length = img.segments.length + 1 := by
    simp [phdrsOf]
  have hhs : headerSize (img.segments.length + 1) ≤ dataStart (2 ^ pageBits) img :=
    le_chunkLen hP _
  have hlen : (fileBytes c (2 ^ pageBits) img).length =
      dataStart (2 ^ pageBits) img + (blob (2 ^ pageBits) img.segments).length := by
    simp only [fileBytes, List.length_append, encodeEhdr_length, encodePhdrs_length, hn',
      zeros_length]
    simp only [headerSize, EHDR_SIZE] at hhs ⊢; omega
  have hfe : (ehdrOf c img (phdrsOf (2 ^ pageBits) img).length).fits = true := by
    have := img.entry.toNat_lt
    simp only [Ehdr.fits, Bool.and_eq_true, fits_iff]
    simp only [ehdrOf, hn', Nat.reducePow, ET_EXEC, EV_CURRENT, EHDR_SIZE, PHDR_SIZE, SHDR_SIZE]
    omega
  have hfp : (phdrsOf (2 ^ pageBits) img).all Phdr.fits = true := by
    simp only [phdrsOf, List.all_append, Bool.and_eq_true]
    refine ⟨layout_fits hP hP64 _ _ hmem (by omega), ?_⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true, Phdr.fits, Bool.and_eq_true,
      fits_iff]
    simp only [stackPhdr, Nat.reducePow, PT_GNU_STACK, PF_R, PF_W]
    omega
  unfold write
  simp [hok, hfe, hfp]

end Millipede.Elf
