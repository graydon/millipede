import Millipede.Object.Pe.Write
import Millipede.Object.Pe.Load
import Millipede.Object.Elf.Laws
import Millipede.Object.Format

/-!
# Laws of the PE32+ format

The main law is `parse_write`: what the writer wrote, the loader model reads back as the image
the writer was given, with each section's bytes followed by the zeros of its file padding, the
image base, the headers, the import section and the import list of the configuration. From it
follow `load_write`, which says that loading the written bytes gives exactly the image's initial
machine state, and `loadWith_write`, which says what the fuller model maps when the imports
resolve, and `iatSlots`, which says that slot `k` of the import address table then holds the
address of function `k` on a read-only page. `write_valid` says that the writer accepts only
valid images.

`Pe.format c abi` is the `Format isa abi` value and `Pe.laws` proves its `Format.Laws`.
`Pe.win64 abi` is the instance for x64 Windows.
-/

namespace Millipede.Pe

open Millipede.Elf (zeros zeros_length chunkLen pad blob le_chunkLen chunkLen_mod pad_add
  all_zeros)

/-! ### Strings and lookup tables -/

theorem cstr_append {nm rest : List UInt8} (h : nm.all (· != 0) = true) :
    cstr (nm ++ 0 :: rest) = some nm := by
  have h' : ∀ a ∈ nm, (a != 0) = true := by simpa using h
  simp [cstr, List.takeWhile_append_of_pos h']

@[simp] theorem thunks_length (R : Nat) : ∀ os : List Nat, (thunks R os).length = 8 * (os.length + 1)
  | [] => rfl
  | o :: os => by simp [thunks, thunks_length R os]; omega

@[simp] theorem nameOffsets_length : ∀ (off : Nat) (nms : List (List UInt8)),
    (nameOffsets off nms).length = nms.length
  | _, [] => rfl
  | _, _ :: nms => by simp [nameOffsets, nameOffsets_length _ nms]

/-- What a lookup table entry of the writer points at: a hint/name entry at or after `lo`, inside
the import section, holding the name `nm`, which has no zero byte. -/
def NameAt (sec : List UInt8) (R lo : Nat) (o : Nat) (nm : List UInt8) : Prop :=
  lo ≤ o ∧ 0 < o ∧ R + o < 2 ^ 31 ∧ nm.all (· != 0) = true ∧ ∃ rest, sec.drop (o + 2) = nm ++ 0 :: rest

/-- Each offset points at its name. -/
def NamesAt (sec : List UInt8) (R lo : Nat) : List Nat → List (List UInt8) → Prop
  | [], [] => True
  | o :: os, nm :: nms => NameAt sec R lo o nm ∧ NamesAt sec R lo os nms
  | _, _ => False

/-- The lookup table at offset `off` reads back as the names. -/
theorem readNames_thunks (sec : List UInt8) (R lo : Nat) :
    ∀ (os : List Nat) (nms : List (List UInt8)), NamesAt sec R lo os nms →
    ∀ (fuel off : Nat) (B : List UInt8), os.length < fuel → sec.drop off = thunks R os ++ B →
    readNames sec R lo fuel off = some nms
  | [], [], _, fuel + 1, off, B, _, hd => by
    have hl : off + 8 ≤ sec.length := by
      have := congrArg List.length hd; simp [thunks] at this; omega
    have he : (sec.drop off).take 8 = natBytes 8 0 := by rw [hd]; exact List.take_left' rfl
    simp [readNames, hl, he, natOfBytes_natBytes]
  | o :: os, nm :: nms, ⟨⟨hlo, ho, hR, hnm, rest, hrest⟩, hf⟩, fuel + 1, off, B, hfu, hd => by
    have hl : off + 8 ≤ sec.length := by
      have := congrArg List.length hd; simp [thunks] at this; omega
    have he : natOfBytes ((sec.drop off).take 8) = R + o := by
      rw [hd, thunks, List.append_assoc, List.take_left' (natBytes_length 8 _),
        natOfBytes_natBytes, Nat.mod_eq_of_lt (by omega)]
    have hd' : sec.drop (off + 8) = thunks R os ++ B := by
      rw [← List.drop_drop, hd, thunks, List.append_assoc, List.drop_left' (natBytes_length 8 _)]
    have ih := readNames_thunks sec R lo os nms hf fuel (off + 8) B (by simp at hfu; omega) hd'
    have hc : cstr (sec.drop (R + o - R + 2)) = some nm := by
      rw [show R + o - R + 2 = o + 2 by omega, hrest]; exact cstr_append hnm
    simp only [readNames, hl, ite_true, he, hc, ih]
    simp only [ite_eq_right (show ¬ R + o = 0 by omega), ite_eq_left (show R + lo ≤ R + o ∧ R + o < 2 ^ 31 by omega)]

/-- The hint/name entries of the writer hold the names at their offsets. -/
theorem nameTable_at (sec : List UInt8) (R lo : Nat) : ∀ (off : Nat) (nms : List (List UInt8)),
    sec.drop off = nameTable nms → lo ≤ off → 0 < off → R + sec.length < 2 ^ 31 →
    nms.all (fun nm => nm.all (· != 0)) = true →
    NamesAt sec R lo (nameOffsets off nms) nms
  | _, [], _, _, _, _, _ => trivial
  | off, nm :: nms, hd, hlo, ho, hR, hnm => by
    simp only [List.all_cons, Bool.and_eq_true] at hnm
    have hlen : off + (nameEntry nm).length ≤ sec.length := by
      have := congrArg List.length hd
      have h0 : 0 < (nameEntry nm).length := by simp [nameEntry]
      rw [List.length_drop, nameTable, List.length_append] at this; omega
    refine ⟨⟨hlo, ho, ?_, hnm.1, zeros ((nm.length + 1) % 2) ++ nameTable nms, ?_⟩,
      nameTable_at sec R lo _ nms ?_ (by omega) (by omega) hR hnm.2⟩
    · simp [nameEntry] at hlen; omega
    · rw [← List.drop_drop, hd]; simp [nameTable, nameEntry]
    · rw [← List.drop_drop, hd, nameTable, List.drop_left' rfl]

/-! ### The import section round trip -/

/-- The import section's checks that the writer makes. -/
def idataFits (c : Config) (R : Nat) : Prop :=
  nameOk c.dll = true ∧ c.funcs.all nameOk = true ∧ fieldsFit (descOf c R) = true ∧
    R + (idata c R).length < 2 ^ 31

theorem nameOk_all {nm : List UInt8} (h : nameOk nm = true) : nm.all (· != 0) = true := by
  simp only [nameOk, Bool.and_eq_true] at h; exact h.2

/-- The loader model reads the writer's import section back as the configured imports. -/
theorem parseImports_idata (c : Config) (R : Nat) (h : idataFits c R) :
    parseImports R (idata c R) = some ⟨c.dll, c.funcs, R + iatOff c.funcs.length⟩ := by
  obtain ⟨hdll, hfuncs, hfit, hR⟩ := h
  let n := c.funcs.length
  let offs := importOffsets c
  have hoffs : offs.length = n := by simp [offs, importOffsets, n]
  let sec := idata c R
  -- the pieces of the section and their offsets
  have hsec : sec = putFields (descOf c R) ++ (zeros DESC_LEN ++ (thunks R offs ++
      (thunks R offs ++ (dllEntry c.dll ++ nameTable c.funcs)))) := by
    simp [sec, idata, offs]
  have hdl : (putFields (descOf c R)).length = DESC_LEN := by simp [descOf, descFields, DESC_LEN]
  have hg : getFields descWidths sec = [R + 40, 0, 0, R + dllOff n, R + iatOff n] := by
    rw [hsec]; exact getFields_putFields (descOf c R) hfit _
  have hz : (sec.drop DESC_LEN).take DESC_LEN = zeros DESC_LEN := by
    rw [hsec, List.drop_left' hdl, List.take_left' (zeros_length _)]
  have hilt : sec.drop 40 = thunks R offs ++ (thunks R offs ++ (dllEntry c.dll ++ nameTable c.funcs)) := by
    rw [hsec, show 40 = DESC_LEN + DESC_LEN from rfl, ← List.drop_drop, List.drop_left' hdl,
      List.drop_left' (zeros_length _)]
  have hdllAt : sec.drop (dllOff n) = dllEntry c.dll ++ nameTable c.funcs := by
    rw [show dllOff n = 40 + 8 * (offs.length + 1) + 8 * (offs.length + 1) by
      simp [dllOff, hoffs]; omega, ← List.drop_drop, ← List.drop_drop, hilt,
      List.drop_left' (thunks_length _ _), List.drop_left' (thunks_length _ _)]
  have hnamesAt : sec.drop (dllOff n + (dllEntry c.dll).length) = nameTable c.funcs := by
    rw [← List.drop_drop, hdllAt, List.drop_left' rfl]
  have hlenR : R + sec.length < 2 ^ 31 := hR
  have hf2 := nameTable_at sec R (dllOff n) _ c.funcs hnamesAt (by omega) (by unfold dllOff; omega)
    hlenR (by simpa [List.all_eq_true] using fun nm hm => nameOk_all ((List.all_eq_true.mp hfuncs) nm hm))
  have hrn : readNames sec R (dllOff n) sec.length 40 = some c.funcs := by
    refine readNames_thunks sec R (dllOff n) offs c.funcs hf2 _ 40 _ ?_ hilt
    have := congrArg List.length hilt
    simp at this; omega
  have hcs : cstr (sec.drop (dllOff n)) = some c.dll := by
    rw [hdllAt, dllEntry, List.append_assoc, List.append_assoc, List.singleton_append]
    exact cstr_append (nameOk_all hdll)
  show parseImports R sec = _
  unfold parseImports
  rw [hg]
  simp only [show R + dllOff n - R = dllOff n by omega, show R + 40 - R = 40 by omega, hrn, hcs]
  have h1 : R + 2 * DESC_LEN ≤ R + 40 ∧ R ≤ R + iatOff n ∧ R ≤ R + dllOff n := by
    simp only [DESC_LEN]; omega
  have h2 : R + 40 + 8 * (c.funcs.length + 1) ≤ R + iatOff n ∧
      R + iatOff n + 8 * (c.funcs.length + 1) ≤ R + dllOff n := by
    simp only [iatOff, dllOff, n]; omega
  simp only [hz, h1, h2, and_self, ite_true, n]

/-! ### Sections round trip -/

/-- A segment as the loader model reads it back: its bytes followed by the zeros of the file
padding, up to its size in memory. -/
def filed (sg : Segment) : Segment :=
  { sg with
    bytes := List.take (min (chunkLen FA sg.bytes.length) sg.memSize)
      (sg.bytes ++ zeros (pad FA sg.bytes.length)) }

theorem zero_tail (p k : Nat) (rest : List UInt8) :
    (((zeros p ++ rest).drop k).take (p - k)).all (· == 0) = true := by
  by_cases hk : k ≤ p
  · rw [List.drop_append_of_le_length (by simpa using hk), zeros, List.drop_replicate,
      List.take_left' (by simp)]
    simp [List.all_replicate]
  · simp [show p - k = 0 by omega]

theorem FA_pos : 0 < FA := by decide

/-- A segment's section header, read against a file that holds the segment's padded bytes at its
offset, gives back the segment with its padding. -/
theorem secSeg_secShdr {base : Nat} (pre rest : List UInt8) (sg : Segment)
    (hoff : pre.length % FA = 0) (hle : sg.bytes.length ≤ sg.memSize)
    (hb : base ≤ sg.vaddr.toNat) :
    secSeg base (pre ++ (sg.bytes ++ (zeros (pad FA sg.bytes.length) ++ rest))) pre.length
      (secShdr base pre.length sg) = some (filed sg) := by
  have hc := pad_add FA_pos sg.bytes.length
  have hz : ((List.drop (pre.length + sg.memSize)
      (pre ++ (sg.bytes ++ (zeros (pad FA sg.bytes.length) ++ rest)))).take
        (chunkLen FA sg.bytes.length - sg.memSize)).all (· == 0) = true := by
    rw [← List.drop_drop, List.drop_left' rfl, List.drop_append, List.drop_eq_nil_of_le hle,
      List.nil_append, show chunkLen FA sg.bytes.length - sg.memSize =
        pad FA sg.bytes.length - (sg.memSize - sg.bytes.length) by omega]
    exact zero_tail _ _ _
  unfold secSeg
  rw [ite_eq_left ⟨Nat.le_refl _, hoff, chunkLen_mod _ _, by simp [secShdr]; omega, charsOk_permChars _, hz⟩]
  simp only [secShdr, filed, List.drop_left' rfl, charsPerm_permChars,
    show base + (sg.vaddr.toNat - base) = sg.vaddr.toNat by omega, UInt64.ofNat_toNat]
  rw [← List.append_assoc, List.take_append_of_le_length (by simp; omega)]

@[simp] theorem shdrsOf_length (base : Nat) : ∀ (off : Nat) (segs : List Segment),
    (shdrsOf base off segs).length = segs.length
  | _, [] => rfl
  | _, _ :: sgs => by simp [shdrsOf, shdrsOf_length base _ sgs]

/-- The section headers that `shdrsOf` produces, read against a file that holds `blob` at their
offset, give back the segments with their padding. -/
theorem secSegs_shdrsOf {base : Nat} : ∀ (segs : List Segment) (pre : List UInt8),
    pre.length % FA = 0 → (∀ sg ∈ segs, sg.bytes.length ≤ sg.memSize ∧ base ≤ sg.vaddr.toNat) →
    secSegs base (pre ++ blob FA segs) pre.length (shdrsOf base pre.length segs) =
      some (segs.map filed)
  | [], _, _, _ => rfl
  | sg :: sgs, pre, hoff, hok => by
    have e : pre ++ blob FA (sg :: sgs) =
        (pre ++ (sg.bytes ++ zeros (pad FA sg.bytes.length))) ++ blob FA sgs := by
      simp [blob]
    have hl : (pre ++ (sg.bytes ++ zeros (pad FA sg.bytes.length))).length =
        pre.length + chunkLen FA sg.bytes.length := by
      simp [List.length_append, ← pad_add FA_pos sg.bytes.length]
    have hoff' : (pre ++ (sg.bytes ++ zeros (pad FA sg.bytes.length))).length % FA = 0 := by
      rw [hl, Nat.add_mod, hoff, chunkLen_mod, Nat.zero_mod]
    have ih := secSegs_shdrsOf sgs _ hoff' (fun s hs => hok s (List.mem_cons_of_mem _ hs))
    rw [hl, ← e] at ih
    have h1 : secSeg base (pre ++ blob FA (sg :: sgs)) pre.length (secShdr base pre.length sg) =
        some (filed sg) := by
      have := secSeg_secShdr (base := base) pre (blob FA sgs) sg hoff
        (hok sg List.mem_cons_self).1 (hok sg List.mem_cons_self).2
      simpa [blob] using this
    simp only [shdrsOf, secSegs, h1, show (secShdr base pre.length sg).rawPtr +
        (secShdr base pre.length sg).rawSize = pre.length + chunkLen FA sg.bytes.length from rfl,
      ih, List.map_cons]

theorem splitLast_append {α : Type} : ∀ (l : List α) (a : α), splitLast (l ++ [a]) = some (l, a)
  | [], _ => rfl
  | [x], a => rfl
  | x :: y :: l, a => by
    simp only [List.cons_append, splitLast]
    rw [← List.cons_append, splitLast_append (y :: l) a]; rfl

/-! ### The padded image -/

theorem filed_getD (sg : Segment) (hle : sg.bytes.length ≤ sg.memSize) (i : Nat) :
    (filed sg).bytes.getD i 0 = sg.bytes.getD i 0 := by
  simp only [filed, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_append]
  by_cases hi : i < sg.bytes.length
  · have := le_chunkLen FA_pos sg.bytes.length
    have : i < min (chunkLen FA sg.bytes.length) sg.memSize := by omega
    simp [hi, this]
  · split <;> simp [hi, zeros, List.getElem?_replicate] <;> split <;> simp <;>
      exact (List.getElem?_eq_none (by omega)).symm ▸ rfl

theorem segByte_map_filed : ∀ (sgs : List Segment), (∀ sg ∈ sgs, sg.bytes.length ≤ sg.memSize) →
    ∀ a, Image.segByte (sgs.map filed) a = Image.segByte sgs a
  | [], _, _ => rfl
  | sg :: sgs, h, a => by
    simp only [List.map_cons, Image.segByte]
    rw [segByte_map_filed sgs (fun s hs => h s (List.mem_cons_of_mem _ hs)) a]
    simp only [Segment.contains, Segment.byteAt, filed_getD sg (h sg List.mem_cons_self)]
    rfl

theorem segPerm_map_filed (pb : Nat) : ∀ (sgs : List Segment) (p : Nat),
    Image.segPerm pb (sgs.map filed) p = Image.segPerm pb sgs p
  | [], _ => rfl
  | sg :: sgs, p => by
    simp only [List.map_cons, Image.segPerm]
    rw [segPerm_map_filed pb sgs p]
    rfl

/-- The image with each segment's bytes padded as the loader model reads them. -/
def padImg (img : Image) : Image := { img with segments := img.segments.map filed }

/-- Padding the bytes with zeros does not change the initial machine state. -/
theorem init_padImg {isa : Isa} (abi : Abi isa) (img : Image)
    (h : ∀ sg ∈ img.segments, sg.bytes.length ≤ sg.memSize) :
    (padImg img).init abi = img.init abi := by
  have hb : (padImg img).byteAt = img.byteAt := funext (segByte_map_filed _ h)
  have hp : (padImg img).pagePerm abi.pageBits abi.stackTop = img.pagePerm abi.pageBits abi.stackTop := by
    funext p; simp only [Image.pagePerm, padImg, segPerm_map_filed]; rfl
  simp only [Image.init, Image.mem, hb, hp]
  rfl

theorem sortedDisjoint_map_filed (pb : Nat) : ∀ sgs : List Segment,
    Image.sortedDisjoint pb (sgs.map filed) = Image.sortedDisjoint pb sgs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp only [List.map_cons, Image.sortedDisjoint]
    rw [← List.map_cons, sortedDisjoint_map_filed pb (b :: rest)]
    rfl

theorem contig_map_filed : ∀ (cur : Nat) (sgs : List Segment),
    contig cur (sgs.map filed) = contig cur sgs
  | _, [] => rfl
  | cur, sg :: sgs => by
    simp only [List.map_cons, contig]; rw [contig_map_filed _ sgs]; rfl

theorem nextAddr_map_filed : ∀ (cur : Nat) (sgs : List Segment),
    nextAddr cur (sgs.map filed) = nextAddr cur sgs
  | _, [] => rfl
  | cur, sg :: sgs => by
    simp only [List.map_cons, nextAddr]; rw [nextAddr_map_filed _ sgs]; rfl

theorem segOk_filed {pb lim : Nat} {sg : Segment} (h : Image.segOk pb lim sg = true) :
    Image.segOk pb lim (filed sg) = true := by
  have hl : (filed sg).bytes.length ≤ sg.memSize := by simp [filed]; omega
  simp only [Image.segOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨⟨⟨h.1.1.1.1, hl⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem imgOk_padImg {c : Config} {pb : Nat} {top : UInt64} {base : Nat} {img : Image}
    (h : imgOk c pb top base img = true) : imgOk c pb top base (padImg img) = true := by
  simp only [imgOk, Elf.validAt, padImg, List.all_map, contig_map_filed,
    sortedDisjoint_map_filed, List.isEmpty_map, Image.stackPages, Bool.and_eq_true,
    List.all_eq_true, Function.comp] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨h1, ⟨⟨⟨⟨hA, hB⟩, hC⟩, (fun sg hs => segOk_filed (hD sg hs))⟩, hE⟩⟩, h3⟩, h4⟩, h5⟩,
    h6⟩, h7⟩, h8⟩

/-! ### Facts from the image check -/

theorem le_pageUp (a : Nat) : a ≤ pageUp a := le_chunkLen (by decide) a

theorem contig_ge : ∀ (cur : Nat) (sgs : List Segment), contig cur sgs = true →
    ∀ sg ∈ sgs, cur ≤ sg.vaddr.toNat
  | _, [], _, _, h => by cases h
  | cur, sg :: sgs, h, s, hs => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.mp hs with rfl | hs
    · omega
    · have := contig_ge _ sgs h.2 s hs
      have := le_pageUp (sg.vaddr.toNat + sg.memSize)
      omega

theorem nextAddr_ge : ∀ (cur : Nat) (sgs : List Segment), contig cur sgs = true →
    cur ≤ nextAddr cur sgs
  | _, [], _ => Nat.le_refl _
  | cur, sg :: sgs, h => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq] at h
    have := nextAddr_ge _ sgs h.2
    have := le_pageUp (sg.vaddr.toNat + sg.memSize)
    simp only [nextAddr]; omega


/-! ### The round trip -/

/-- How `parse` succeeds, step by step. -/
theorem parse_of {c : Config} {pb : Nat} {top : UInt64} {bs : List UInt8} {h : Hdr}
    {shs : List Shdr} {segs prog : List Segment} {id : Segment} {im : Imports}
    (h1 : getFields hdrWidths bs = (hdrFields h).map Prod.snd)
    (h2 : hdrOk c h bs.length = true)
    (h3 : decodeShdrs h.nsec (bs.drop HDR_LEN) = some shs)
    (h4 : secSegs h.base bs h.sizeOfHeaders shs = some segs)
    (h5 : splitLast segs = some (prog, id))
    (h6 : parseImports (id.vaddr.toNat - h.base) id.bytes = some im)
    (h7 : imgOk c pb top h.base (⟨prog, UInt64.ofNat (h.base + h.entry), h.stackReserve - c.stackMargin⟩ : Image) = true)
    (h8 : idataOk top h (⟨prog, UInt64.ofNat (h.base + h.entry), h.stackReserve - c.stackMargin⟩ : Image) id im = true) :
    parse c pb top bs = some
      { img := ⟨prog, UInt64.ofNat (h.base + h.entry), h.stackReserve - c.stackMargin⟩,
        base := h.base, idata := id, imports := im,
        headers := ⟨UInt64.ofNat h.base, bs.take h.sizeOfHeaders, h.sizeOfHeaders, Perm.r_⟩ } := by
  simp only [parse, h1, Hdr.ofFields_hdrFields, h2, and_self, ite_true, h3, h4, h5, h6, h7, h8]

/-- `write` succeeds only on a checked image, and then returns `fileBytes`. -/
theorem write_inv {c : Config} {pb : Nat} {top : UInt64} {img : Image} {bs : List UInt8}
    (h : write c pb top img = .ok bs) :
    imgOk c pb top (baseOf img) img = true ∧ fileOk c top img = true ∧ bs = fileBytes c img := by
  unfold write at h; grind

/-- What the loader model reads from the file of `img`. -/
def expected (c : Config) (img : Image) : Parsed where
  img := padImg img
  base := baseOf img
  headers := ⟨UInt64.ofNat (baseOf img), (fileBytes c img).take (headerSize img), headerSize img,
    Perm.r_⟩
  idata := idataSeg c img
  imports := ⟨c.dll, c.funcs, idataRva img + iatOff c.funcs.length⟩

theorem filed_idataSeg (c : Config) (img : Image) : filed (idataSeg c img) = idataSeg c img := by
  have := le_chunkLen FA_pos (idata c (idataRva img)).length
  simp only [filed, idataSeg, Nat.min_eq_right this]
  rw [List.take_left' rfl]

theorem chunkLen_FA_le {x : Nat} (h : x ≤ SA) : chunkLen FA x ≤ SA := by
  simp only [chunkLen, FA, SA] at h ⊢; omega

/-- The loader model parses what the writer wrote into the image the writer was given, with each
section's bytes followed by its file padding, and the configured imports. -/
theorem parse_write {c : Config} {pb : Nat} {top : UInt64} {img : Image} {bs : List UInt8}
    (h : write c pb top img = .ok bs) : parse c pb top bs = some (expected c img) := by
  obtain ⟨hok, hfo, rfl⟩ := write_inv h
  have hok' := hok
  simp only [fileOk, Bool.and_eq_true, decide_eq_true_eq] at hfo
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbelow, hhl⟩, hent⟩, h31⟩, hdll⟩, _⟩, hfuncs⟩, hfh⟩, hfs⟩, hfd⟩ := hfo
  simp only [imgOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hv⟩, _⟩, _⟩, _⟩, hcont⟩, _⟩, _⟩ := hok'
  have hle := Elf.validAt_bytes_le hv
  simp only [List.all_eq_true, decide_eq_true_eq] at hle
  have hge := contig_ge _ _ hcont
  have hnext := nextAddr_ge _ _ hcont
  have hsb : stackBottom top img ≤ top.toNat := by
    unfold stackBottom SA
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.div_mul_le_self _ _)
  have htop := top.toNat_lt
  have hpu := le_pageUp (idata c (idataRva img)).length
  have hidv : (idataSeg c img).vaddr.toNat = baseOf img + idataRva img := by
    simp only [hdrOf] at hbelow
    exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  -- the file
  let H := headerSize img
  let secs := sectionsOf c img
  let shs := shdrsOf (baseOf img) H secs
  let hd := hdrOf c img
  let gap := zeros (H - (HDR_LEN + SHDR_LEN * nsecOf img))
  have hfile : fileBytes c img =
      putFields (hdrFields hd) ++ (encodeShdrs shs ++ (gap ++ blob FA secs)) := by
    simp [fileBytes, hd, shs, secs, gap, H]
  have hHle : HDR_LEN + SHDR_LEN * nsecOf img ≤ H := le_chunkLen FA_pos _
  have hhdl : (putFields (hdrFields hd)).length = HDR_LEN := by
    rw [putFields_length, hdrFields_widths]; rfl
  have hns : shs.length = nsecOf img := by simp [shs, secs, sectionsOf, nsecOf]
  have hpre : (putFields (hdrFields hd) ++ (encodeShdrs shs ++ gap)).length = H := by
    simp only [List.length_append, hhdl, encodeShdrs_length, hns, gap, zeros_length]; omega
  have hlen : H ≤ (fileBytes c img).length := by
    have : (fileBytes c img).length = H + (blob FA secs).length := by
      rw [hfile]; simp only [List.length_append] at hpre ⊢; omega
    omega
  -- 1, 2: the headers
  have h1 : getFields hdrWidths (fileBytes c img) = (hdrFields hd).map Prod.snd := by
    rw [hfile, ← hdrFields_widths hd]; exact getFields_putFields _ hfh _
  have h2 : hdrOk c hd (fileBytes c img).length = true := by
    simp only [hdrOk, hd, hdrOf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨chunkLen_mod _ _, hHle⟩, chunkLen_FA_le hhl⟩, hlen⟩, trivial⟩, by omega⟩
  -- 3: the section table
  have h3 : decodeShdrs hd.nsec ((fileBytes c img).drop HDR_LEN) = some shs := by
    rw [hfile, List.drop_left' hhdl, show hd.nsec = shs.length from hns.symm]
    exact decodeShdrs_encodeShdrs shs hfs _
  -- 4: the sections
  have h4 : secSegs hd.base (fileBytes c img) hd.sizeOfHeaders shs = some (secs.map filed) := by
    have := secSegs_shdrsOf (base := baseOf img) secs
      (putFields (hdrFields hd) ++ (encodeShdrs shs ++ gap)) (by rw [hpre]; exact chunkLen_mod _ _)
      (by
        intro sg hs
        simp only [secs, sectionsOf, List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact ⟨hle sg hs, by have := hge sg hs; omega⟩
        · exact ⟨Nat.le_refl _, by rw [hidv]; omega⟩)
    rw [hpre] at this
    rw [hfile]
    change secSegs (baseOf img) _ H (shdrsOf (baseOf img) H secs) = _
    simpa [List.append_assoc] using this
  -- 5: the import section is last
  have h5 : splitLast (secs.map filed) = some (img.segments.map filed, idataSeg c img) := by
    simp only [secs, sectionsOf, List.map_append, List.map_cons, List.map_nil, filed_idataSeg]
    exact splitLast_append _ _
  -- 6: the imports
  have h6 : parseImports ((idataSeg c img).vaddr.toNat - hd.base) (idataSeg c img).bytes =
      some ⟨c.dll, c.funcs, idataRva img + iatOff c.funcs.length⟩ := by
    rw [hidv, show hd.base = baseOf img from rfl, Nat.add_sub_cancel_left]
    exact parseImports_idata c _ ⟨hdll, hfuncs, hfd, h31⟩
  -- 7, 8: the image and the import section
  have himg : (⟨img.segments.map filed, UInt64.ofNat (hd.base + hd.entry),
      hd.stackReserve - c.stackMargin⟩ : Image) = padImg img := by
    simp only [padImg, hd, hdrOf, Nat.add_sub_cancel, show baseOf img + (img.entry.toNat - baseOf img)
      = img.entry.toNat by omega, UInt64.ofNat_toNat]
  have h7 := imgOk_padImg hok
  have h8 : idataOk top hd (padImg img) (idataSeg c img)
      ⟨c.dll, c.funcs, idataRva img + iatOff c.funcs.length⟩ = true := by
    have hidv' : (UInt64.ofNat (baseOf img + idataRva img)).toNat = baseOf img + idataRva img :=
      hidv
    simp only [idataOk, padImg, nextAddr_map_filed, hd, hdrOf, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, idataSeg, hidv', Nat.add_sub_cancel_left, and_true]
    exact ⟨by simp only [idataRva]; omega, hbelow⟩
  rw [← himg] at h7 h8
  rw [parse_of h1 h2 h3 h4 h5 h6 h7 h8, himg]
  rfl

/-- Loading what the PE writer produced gives exactly the image's initial machine state. -/
theorem load_write {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    (h : write c abi.pageBits abi.stackTop img = .ok bs) : load c abi bs = some (img.init abi) := by
  obtain ⟨hok, _, _⟩ := write_inv h
  simp only [imgOk, Bool.and_eq_true] at hok
  have hle := Elf.validAt_bytes_le hok.1.1.1.1.1.1.2
  simp only [List.all_eq_true, decide_eq_true_eq] at hle
  simp only [load, parse_write h, Option.map_some, expected, init_padImg abi img hle]

/-- The writer refuses invalid images. -/
theorem write_valid {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    (h : write c abi.pageBits abi.stackTop img = .ok bs) : img.valid abi = true := by
  obtain ⟨hok, _, _⟩ := write_inv h
  simp only [imgOk, Bool.and_eq_true] at hok
  rw [Elf.valid_eq]; exact hok.1.1.1.1.1.1.2

/-- With the imports resolved to `addrs`, the fuller model maps what the writer laid out: the
headers, the program's sections, and the import section with slot `k` of its address table
holding the address of function `k`. -/
theorem loadWith_write {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    {resolve : List UInt8 → List UInt8 → Option UInt64} {addrs : List UInt64}
    (h : write c abi.pageBits abi.stackTop img = .ok bs)
    (hr : resolveAll resolve c.dll c.funcs = some addrs) :
    loadWith c abi resolve bs = some (((expected c img).withImports addrs).init abi) := by
  simp only [loadWith, parse_write h, expected, hr, Option.map_some]

/-! ### The address table after loading -/

/-- `fillSlots` writes the addresses, 8 bytes each, from `off` on. -/
theorem fillSlots_eq : ∀ (as : List UInt64) (sec : List UInt8) (off : Nat),
    off + 8 * as.length ≤ sec.length →
    fillSlots sec off as = sec.take off ++ as.flatMap (fun a => natBytes 8 a.toNat) ++
      sec.drop (off + 8 * as.length)
  | [], sec, off, _ => by simp [fillSlots]
  | a :: as, sec, off, h => by
    simp only [List.length_cons] at h
    rw [fillSlots, fillSlots_eq as _ (off + 8) (by rw [patchBytes_length]; omega),
      patchBytes_eq _ _ _ (by rw [natBytes_length]; omega), natBytes_length]
    have hl : (sec.take off ++ natBytes 8 a.toNat).length = off + 8 := by simp; omega
    rw [List.take_left' hl, show off + 8 + 8 * as.length = (off + 8) + 8 * as.length from rfl,
      ← List.drop_drop, List.drop_left' hl, List.drop_drop]
    simp only [List.flatMap_cons, List.append_assoc, List.length_cons, Nat.mul_succ]
    grind

@[simp] theorem slots_length : ∀ as : List UInt64,
    (as.flatMap (fun a => natBytes 8 a.toNat)).length = 8 * as.length
  | [] => rfl
  | a :: as => by simp [List.flatMap_cons, slots_length as]; omega

/-- Byte `i` of slot `k` of the written addresses. -/
theorem flatMap_slot : ∀ (as : List UInt64) (k i : Nat), k < as.length → i < 8 →
    (as.flatMap (fun a => natBytes 8 a.toNat))[8 * k + i]? = (natBytes 8 as[k]!.toNat)[i]?
  | [], _, _, h, _ => by simp at h
  | a :: as, 0, i, _, hi => by
    simp [List.getElem?_append_left (show i < (natBytes 8 a.toNat).length by simpa using hi)]
  | a :: as, k + 1, i, hk, hi => by
    simp only [List.flatMap_cons, List.length_cons] at hk ⊢
    rw [List.getElem?_append_right (by simp; omega), natBytes_length,
      show 8 * (k + 1) + i - 8 = 8 * k + i by omega, flatMap_slot as k i (by omega) hi]
    simp

theorem resolveAll_length (resolve : List UInt8 → List UInt8 → Option UInt64) (dll : List UInt8) :
    ∀ (fs : List (List UInt8)) (as : List UInt64), resolveAll resolve dll fs = some as →
    as.length = fs.length
  | [], as, h => by simp [resolveAll] at h; simp [← h]
  | f :: fs, as, h => by
    simp only [resolveAll] at h
    split at h
    · cases h; simp [resolveAll_length resolve dll fs _ ‹_›]
    · cases h

theorem contig_end : ∀ (cur : Nat) (sgs : List Segment), contig cur sgs = true →
    ∀ sg ∈ sgs, sg.vaddr.toNat + sg.memSize ≤ nextAddr cur sgs
  | _, [], _, _, h => by cases h
  | cur, sg :: sgs, h, s, hs => by
    simp only [contig, Bool.and_eq_true, beq_iff_eq] at h
    have := nextAddr_ge _ sgs h.2
    rcases List.mem_cons.mp hs with rfl | hs
    · have := le_pageUp (s.vaddr.toNat + s.memSize); simp only [nextAddr]; omega
    · exact contig_end _ sgs h.2 s hs

theorem nextAddr_mod : ∀ (cur : Nat) (sgs : List Segment), cur % SA = 0 → nextAddr cur sgs % SA = 0
  | _, [], h => h
  | _, _ :: sgs, _ => nextAddr_mod _ sgs (chunkLen_mod _ _)

theorem init_permAt {isa : Isa} (abi : Abi isa) (img : Image) (a : UInt64) :
    (img.init abi).mem.permAt a = img.pagePerm abi.pageBits abi.stackTop (a.toNat / 2 ^ abi.pageBits) :=
  rfl

theorem withImports_segments (p : Parsed) (addrs : List UInt64) :
    (p.withImports addrs).segments = (p.headers :: p.img.segments) ++
      [{ p.idata with bytes := fillSlots p.idata.bytes (p.imports.iat - (p.idata.vaddr.toNat - p.base)) addrs }] :=
  rfl

theorem coversPage_of {sg : Segment} {p : Nat} (h0 : 0 < sg.memSize)
    (h1 : sg.vaddr.toNat / 2 ^ 12 ≤ p) (h2 : p ≤ (sg.vaddr.toNat + sg.memSize - 1) / 2 ^ 12) :
    sg.coversPage 12 p = true := by
  simp [Segment.coversPage, Segment.firstPage, Segment.lastPage, h0, h1, h2]

/-- An address at or past the page-aligned end `e` of segments is in none of them. -/
theorem segByte_past (a : UInt64) (e : Nat) (he : e % SA = 0) (ha : e ≤ a.toNat) :
    ∀ (l : List Segment), (∀ sg ∈ l, sg.vaddr.toNat + sg.memSize ≤ e) → ∀ r : List Segment,
    Image.segByte (l ++ r) a = Image.segByte r a ∧
      Image.segPerm 12 (l ++ r) (a.toNat / 2 ^ 12) = Image.segPerm 12 r (a.toNat / 2 ^ 12)
  | [], _, _ => ⟨rfl, rfl⟩
  | sg :: l, h, r => by
    have h1 := h sg List.mem_cons_self
    have ih := segByte_past a e he ha l (fun s hs => h s (List.mem_cons_of_mem _ hs)) r
    have hc : sg.contains a = false := by simp [Segment.contains]; omega
    have hp : sg.coversPage 12 (a.toNat / 2 ^ 12) = false := by
      simp only [SA] at he
      by_cases hm : sg.memSize = 0
      · simp [Segment.coversPage, hm]
      · have : ¬ a.toNat / 2 ^ 12 ≤ (sg.vaddr.toNat + sg.memSize - 1) / 2 ^ 12 := by
          simp only [Nat.reducePow]; omega
        simp [Segment.coversPage, Segment.lastPage, this]
    simp only [List.cons_append, Image.segByte, Image.segPerm, hc, hp, ih]
    exact ⟨rfl, rfl⟩

/-- Byte `i` of slot `k` after `fillSlots` is byte `i` of address `k`. -/
theorem fillSlots_slot (as : List UInt64) (sec : List UInt8) (off k i : Nat)
    (h : off + 8 * as.length ≤ sec.length) (hk : k < as.length) (hi : i < 8) :
    (fillSlots sec off as)[off + 8 * k + i]? = (natBytes 8 as[k]!.toNat)[i]? := by
  rw [fillSlots_eq as sec off h, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by rw [slots_length, List.length_take]; omega), List.length_take,
    show off + 8 * k + i - min off sec.length = 8 * k + i by omega]
  exact flatMap_slot as k i hk hi

/-- Where the writer puts the import section: on a page boundary, past the end of the headers
and of every program section, with its end below the stack top, for 4 KiB pages. -/
theorem idata_place {c : Config} {pb : Nat} {top : UInt64} {img : Image} {bs : List UInt8}
    (hw : write c pb top img = .ok bs) :
    pb = 12 ∧ (baseOf img + idataRva img) % SA = 0 ∧
      baseOf img + idataRva img + (idata c (idataRva img)).length ≤ top.toNat ∧
      ∀ sg ∈ (expected c img).headers :: (expected c img).img.segments,
        sg.vaddr.toNat + sg.memSize ≤ baseOf img + idataRva img := by
  obtain ⟨hok, hfo, -⟩ := write_inv hw
  simp only [fileOk, Bool.and_eq_true, decide_eq_true_eq] at hfo
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbelow, hhl⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hfo
  simp only [imgOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hpb, -⟩, -⟩, hal⟩, -⟩, hcont⟩, -⟩, -⟩ := hok
  have hnext := nextAddr_ge _ _ hcont
  have hBR : nextAddr (baseOf img + SA) img.segments = baseOf img + idataRva img := by
    simp only [idataRva]; omega
  have hsb : stackBottom top img ≤ top.toNat := by
    unfold stackBottom SA
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.div_mul_le_self _ _)
  have htop := top.toNat_lt
  have hpu := le_pageUp (idata c (idataRva img)).length
  simp only [hdrOf] at hbelow
  refine ⟨hpb, by rw [← hBR]; exact nextAddr_mod _ _ (by simp only [SA] at *; omega),
    by omega, ?_⟩
  intro sg hsg
  simp only [List.mem_cons, expected, padImg, List.mem_map] at hsg
  rcases hsg with rfl | ⟨sg', hm, rfl⟩
  · have := chunkLen_FA_le hhl
    have : (UInt64.ofNat (baseOf img)).toNat = baseOf img := UInt64.toNat_ofNat_of_lt' (by
      simp only [UInt64.size] at htop ⊢; omega)
    simp only [this]; simp only [headerSize] at *; omega
  · have := contig_end _ _ hcont sg' hm; simp only [filed]; omega

/-- In the state that `loadWith_write` gives, the 8 bytes of address table slot `k` are the
address of function `k`, and the slot's page is read-only. -/
theorem iatSlots (c : Config) {isa : Isa} (abi : Abi isa) (img : Image) (bs : List UInt8)
    (resolve : List UInt8 → List UInt8 → Option UInt64) (addrs : List UInt64) (s : MState isa.Regs)
    (hw : write c abi.pageBits abi.stackTop img = .ok bs)
    (hr : resolveAll resolve c.dll c.funcs = some addrs)
    (hs : loadWith c abi resolve bs = some s) :
    ∀ k < addrs.length, ∀ i < 8,
      let a := UInt64.ofNat (baseOf img + idataRva img + iatOff c.funcs.length + 8 * k + i)
      s.mem.bytes a = (natBytes 8 addrs[k]!.toNat)[i]! ∧ s.mem.permAt a = Perm.r_ := by
  intro k hk i hi a
  rw [loadWith_write hw hr] at hs
  cases hs
  obtain ⟨hpb, hmod, hend, hl⟩ := idata_place hw
  have hn := resolveAll_length resolve c.dll c.funcs addrs hr
  -- the import section `sec`, at `B + R`, and slot `k` inside its address table
  generalize hB : baseOf img + idataRva img = BR at hmod hend hl
  have hL : iatOff c.funcs.length + 8 * c.funcs.length < (idata c (idataRva img)).length := by
    simp [idata, descOf, descFields, DESC_LEN, iatOff, importOffsets]; omega
  have htop := abi.stackTop.toNat_lt
  have ha : a.toNat = BR + iatOff c.funcs.length + 8 * k + i := by
    rw [← hB]; exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size] at htop ⊢; omega)
  have hv : (UInt64.ofNat (baseOf img + idataRva img)).toNat = BR := by
    rw [hB]; exact UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size] at htop ⊢; omega)
  have hpast := segByte_past a BR hmod (by omega) _ hl
  have hin : BR ≤ a.toNat ∧ a.toNat < BR + (idata c (idataRva img)).length := by omega
  have e1 : (expected c img).idata = idataSeg c img := rfl
  constructor
  · simp only [Image.init, Image.mem, Image.byteAt, Parsed.withImports]
    rw [(hpast _).1, e1, show (expected c img).base = baseOf img from rfl,
      show (expected c img).imports.iat = idataRva img + iatOff c.funcs.length from rfl]
    simp only [Image.segByte, Segment.contains, Segment.byteAt, idataSeg, hv]
    rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hin), ha,
      show idataRva img + iatOff c.funcs.length - (BR - baseOf img) = iatOff c.funcs.length by
        omega,
      show BR + iatOff c.funcs.length + 8 * k + i - BR = iatOff c.funcs.length + 8 * k + i by
        omega,
      List.getD_eq_getElem?_getD, fillSlots_slot _ _ _ _ _ (by omega) hk hi]
    simp [List.getElem!_eq_getElem?_getD]; rfl
  · rw [init_permAt, hpb, Image.pagePerm, withImports_segments, (hpast _).2, Image.segPerm,
      ite_eq_left (coversPage_of ?_ ?_ ?_)]
    · rfl
    · show 0 < (idata c (idataRva img)).length; omega
    · show (UInt64.ofNat (baseOf img + idataRva img)).toNat / 2 ^ 12 ≤ _
      rw [hv]; exact Nat.div_le_div_right hin.1
    · show _ ≤ ((UInt64.ofNat (baseOf img + idataRva img)).toNat +
        (idata c (idataRva img)).length - 1) / 2 ^ 12
      rw [hv]; exact Nat.div_le_div_right (by omega)

/-! ### The `Format` value -/

/-- The PE32+ format for an ABI, under the platform facts and imports `c`. -/
def format (c : Config) {isa : Isa} (abi : Abi isa) : Format isa abi where
  write := write c abi.pageBits abi.stackTop
  load := load c abi

/-- The PE32+ format satisfies the format laws. -/
theorem laws (c : Config) {isa : Isa} (abi : Abi isa) : (format c abi).Laws where
  write_valid _ _ h := write_valid h
  load_write _ _ h := load_write h

/-- PE32+ for x64 Windows, importing `ExitProcess`, `GetStdHandle`, `WriteFile` and `ReadFile`
from `kernel32.dll`. -/
def win64 {isa : Isa} (abi : Abi isa) : Format isa abi := format Config.win64 abi

theorem win64_laws {isa : Isa} (abi : Abi isa) : (win64 abi).Laws := laws _ abi

end Millipede.Pe
