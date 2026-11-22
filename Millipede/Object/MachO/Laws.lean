import Millipede.Object.MachO.Write
import Millipede.Object.MachO.Load
import Millipede.Object.Elf.Laws
import Millipede.Object.Format

/-!
# Laws of the Mach-O format

The main law is `parse_write`: the loader model reads back the image the writer was given, with
each segment's bytes padded with zeros to whole pages (`padImage`), because the file holds whole
pages and the model reads them as the kernel maps them. Padding changes no byte of the initial
memory (`init_padImage`), so `load_write` says that loading the written bytes gives exactly the
image's initial machine state. `write_valid` says that the writer accepts only valid images.

The proof follows the file from the front: the header (`hdr_ncmds`, `hdr_sizeofcmds`), the load
commands (`decodeCmds_encodeCmds`, `decodeSeg_encodeSeg`, `cmdsOf_facts`), the segments
(`file_layout`, `textSeg_textCmdOf`, `loadSegs_layout`), and the fixed commands, `__LINKEDIT`
and the signature (`TailOk`, `tailOk_write`, `parseCmds_of`). The signature needs no reasoning about SHA-256: the writer appends
`codeSignature` of the bytes before it, and the loader model recomputes it from the same bytes.

`parse_imageOk` says that every file the loader model accepts passes the image check, and
`load_wxorx` that its memory is W^X.

`MachO.format c abi` is the `Format isa abi` value and `MachO.laws` proves its `Format.Laws`.
`MachO.a64Macos abi` is the instance for arm64 macOS.
-/

namespace Millipede.MachO

open Millipede.Elf (takeNat takeNat_natBytes zeros zeros_length chunkLen pad blob validAt
  mod_of_fits fits_iff le_chunkLen chunkLen_mod pad_add)

/-! ### Encodings round-trip -/

/-- A command whose number and size fit 32 bits and whose size is a multiple of 8. -/
def cmdOk (c : Cmd) : Bool :=
  decide (c.cmd < 2 ^ 32) && decide (8 + c.body.length < 2 ^ 32) && c.body.length % 8 == 0

@[simp] theorem encodeCmd_length (c : Cmd) : (encodeCmd c).length = 8 + c.body.length := by
  simp [encodeCmd]; omega

theorem decodeCmds_encodeCmds : ∀ (cs : List Cmd), cs.all cmdOk = true →
    decodeCmds cs.length (encodeCmds cs) = some cs
  | [], _ => by simp [decodeCmds, encodeCmds]
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, cmdOk, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hl : (natBytes 4 c.cmd ++ (natBytes 4 (8 + c.body.length) ++ c.body)).length =
        8 + c.body.length := by simp; omega
    have e : encodeCmds (c :: cs) =
        (natBytes 4 c.cmd ++ (natBytes 4 (8 + c.body.length) ++ c.body)) ++ encodeCmds cs := by
      simp [encodeCmds, encodeCmd]
    have hsz : natOfBytes (((encodeCmds (c :: cs)).drop 4).take 4) = 8 + c.body.length := by
      rw [e, List.append_assoc, List.drop_left' (natBytes_length 4 _), List.append_assoc,
        List.take_left' (natBytes_length 4 _), natOfBytes_natBytes, Nat.mod_eq_of_lt h2]
    simp only [List.length_cons, decodeCmds, hsz]
    have hc : 8 ≤ 8 + c.body.length ∧ (8 + c.body.length) % 8 = 0 ∧
        8 + c.body.length ≤ (encodeCmds (c :: cs)).length :=
      ⟨by omega, by omega, by rw [e, List.length_append, hl]; omega⟩
    rw [ite_eq_left hc, e, List.drop_left' hl, List.take_left' hl, decodeCmds_encodeCmds cs h4]
    simp [List.drop_append, natOfBytes_natBytes, Nat.mod_eq_of_lt h1, List.drop_eq_nil_of_le]

theorem decodeSeg_encodeSeg (s : SegCmd) (hf : s.fits = true) : decodeSeg (encodeSeg s) = s := by
  simp only [SegCmd.fits, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hf
  simp only [decodeSeg, encodeSeg, List.append_assoc, List.take_left' h0, List.drop_left' h0,
    takeNat_natBytes, mod_of_fits h1, mod_of_fits h2, mod_of_fits h3, mod_of_fits h4,
    mod_of_fits h5, mod_of_fits h6, mod_of_fits h7, mod_of_fits h8]

theorem segName_length (p : Perm) : (segName p).length = 16 := by
  unfold segName; repeat' split
  all_goals rfl

theorem sectName_length (p : Perm) : (sectName p).length = 16 := by
  unfold sectName; repeat' split
  all_goals rfl

@[simp] theorem encodeSect_length (p : Perm) (a s o : Nat) :
    (encodeSect p a s o).length = SECT_SIZE := by
  simp [encodeSect, segName_length, sectName_length, SECT_SIZE]

theorem sectOk_encodeSect (p : Perm) {a s o f : Nat} (hs : s < 2 ^ 64) (hf : s ≤ f) :
    sectOk p a o f (encodeSect p a s o) = true := by
  have h32 : (sectName p ++ segName p).length = 32 := by
    simp [segName_length, sectName_length]
  have e : encodeSect p a s o = (sectName p ++ segName p) ++ (natBytes 8 a ++ (natBytes 8 s ++
      (natBytes 4 o ++ (natBytes 4 (sectAlign p) ++ (natBytes 4 0 ++ (natBytes 4 0 ++
      (natBytes 4 (sectFlags p) ++ zeros 12))))))) := by simp [encodeSect]
  have d2 : ((encodeSect p a s o).drop 40).take 8 = natBytes 8 s := by
    rw [e, show 40 = (sectName p ++ segName p).length + 8 by rw [h32], ← List.drop_drop,
      List.drop_left' rfl, List.drop_left' (natBytes_length _ _),
      List.take_left' (natBytes_length _ _)]
  simp only [sectOk, d2, natOfBytes_natBytes, Nat.mod_eq_of_lt hs, beq_self_eq_true, hf,
    decide_true, Bool.and_self]

/-! ### The code signature's size -/

theorem pageHashes_length : ∀ (n : Nat) (bs : List UInt8), bs.length ≤ n →
    (pageHashes n bs).length = 32 * nPages bs.length
  | 0, bs, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | n + 1, bs, h => by
    unfold pageHashes
    split
    · subst_vars; rfl
    · rename_i hne
      have hpos : 0 < bs.length := List.length_pos_iff.mpr hne
      rw [List.length_append, Sha256.hash_length,
        pageHashes_length n _ (by simp only [List.length_drop, CS_PAGE]; omega)]
      simp only [List.length_drop, nPages, CS_PAGE]
      omega

@[simp] theorem beBytes_length (k n : Nat) : (Sha256.beBytes k n).length = k := by
  simp [Sha256.beBytes]

theorem codeSignature_length (code : List UInt8) (e : Nat) :
    (codeSignature code e).length = sigSize code.length := by
  unfold codeSignature
  simp only [List.length_append, beBytes_length]
  simp [identifier, pageHashes_length code.length code (Nat.le_refl _), sigSize]

/-! ### Padded segments

The loader model reads each segment's whole pages from the file, so it gives the segment's bytes
followed by the zero padding that the writer added. Padding changes no byte of memory. -/

/-- A segment with its bytes padded with zeros to whole pages. -/
def padSeg (P : Nat) (sg : Segment) : Segment :=
  { sg with bytes := sg.bytes ++ zeros (pad P sg.bytes.length) }

/-- An image with every segment padded. -/
def padImage (P : Nat) (img : Image) : Image := { img with segments := img.segments.map (padSeg P) }

theorem getD_append_zeros (l : List UInt8) (k i : Nat) :
    (l ++ zeros k)[i]?.getD 0 = l[i]?.getD 0 := by
  by_cases h : i < l.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (show l.length ≤ i by omega)]
    simp only [zeros, List.getElem?_replicate]
    split <;> rfl

theorem segByte_pad (P : Nat) : ∀ (segs : List Segment) (a : UInt64),
    Image.segByte (segs.map (padSeg P)) a = Image.segByte segs a
  | [], _ => rfl
  | sg :: sgs, a => by
    simp only [List.map_cons, Image.segByte, segByte_pad P sgs a]
    have : (padSeg P sg).contains a = sg.contains a := rfl
    rw [this]
    simp [Segment.byteAt, padSeg, getD_append_zeros]

theorem segPerm_pad (P pb : Nat) : ∀ (segs : List Segment) (p : Nat),
    Image.segPerm pb (segs.map (padSeg P)) p = Image.segPerm pb segs p
  | [], _ => rfl
  | sg :: sgs, p => by
    simp only [List.map_cons, Image.segPerm, segPerm_pad P pb sgs p]
    rfl

/-- Padding does not change the initial state. -/
theorem init_padImage {isa : Isa} (abi : Abi isa) (P : Nat) (img : Image) :
    (padImage P img).init abi = img.init abi := by
  have hb : (padImage P img).byteAt = img.byteAt := funext (segByte_pad P img.segments)
  have hp : Image.pagePerm abi.pageBits abi.stackTop (padImage P img) =
      Image.pagePerm abi.pageBits abi.stackTop img := by
    funext p
    simp only [Image.pagePerm, padImage, segPerm_pad, Image.isStackPage, Image.stackPages]
    rfl
  simp only [Image.init, Image.mem, hb, hp]
  rfl

theorem chunkLen_le_iff {P m : Nat} (hP : 0 < P) (hm : m % P = 0) (l : Nat) :
    chunkLen P l ≤ m ↔ l ≤ m := by
  have hl := le_chunkLen hP l
  constructor
  · intro h; omega
  · intro h
    unfold chunkLen
    obtain ⟨q, rfl⟩ : ∃ q, m = P * q := ⟨m / P, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)).symm⟩
    rw [Nat.mul_comm P q]
    apply Nat.mul_le_mul_right
    rw [Nat.div_le_iff_le_mul_add_pred hP]
    have : l ≤ q * P := by rw [Nat.mul_comm]; exact h
    omega

theorem segOk_pad {pb lim : Nat} (sg : Segment) (h : sg.memSize % 2 ^ pb = 0) :
    Image.segOk pb lim (padSeg (2 ^ pb) sg) = Image.segOk pb lim sg := by
  have hc := chunkLen_le_iff (Nat.two_pow_pos pb) h sg.bytes.length
  simp only [Image.segOk, padSeg, List.length_append, zeros_length,
    pad_add (Nat.two_pow_pos pb)]
  simp only [decide_eq_decide.mpr hc]
  rfl

theorem sortedDisjoint_pad (pb P : Nat) : ∀ segs : List Segment,
    Image.sortedDisjoint pb (segs.map (padSeg P)) = Image.sortedDisjoint pb segs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    have := sortedDisjoint_pad pb P (b :: rest)
    simp only [List.map_cons] at this ⊢
    simp only [Image.sortedDisjoint, this]
    rfl

theorem lastEnd_pad (P : Nat) : ∀ segs : List Segment, lastEnd (segs.map (padSeg P)) = lastEnd segs
  | [] => rfl
  | [_] => rfl
  | _ :: b :: rest => by
    have := lastEnd_pad P (b :: rest)
    simp only [List.map_cons] at this ⊢
    simpa [lastEnd] using this

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Padding whole-page segments keeps the image checks. -/
theorem imageOk_pad {c : Config} {pb : Nat} {st : UInt64} {img : Image}
    (h : imageOk c pb st img = true) : imageOk c pb st (padImage (2 ^ pb) img) = true := by
  have hm : ∀ sg ∈ img.segments, sg.memSize % 2 ^ pb = 0 := by
    simp only [imageOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    exact h.1.1.1.1.1.2
  have hall : ∀ (f : Segment → Bool), (∀ sg ∈ img.segments, f (padSeg (2 ^ pb) sg) = f sg) →
      (img.segments.map (padSeg (2 ^ pb))).all f = img.segments.all f := by
    intro f hf
    rw [List.all_map]
    exact all_congr_mem hf
  have hv : validAt pb st (padImage (2 ^ pb) img) = validAt pb st img := by
    simp only [validAt, padImage, Image.stackPages, sortedDisjoint_pad]
    rw [hall _ (fun sg hs => segOk_pad sg (hm sg hs))]
    rfl
  revert h
  unfold imageOk
  rw [hv]
  simp only [padImage]
  rw [hall (fun sg => sg.memSize % 2 ^ pb == 0) (fun _ _ => rfl)]
  clear hv hall hm
  obtain ⟨segs, entry, ss⟩ := img
  cases segs with
  | nil => simp
  | cons s0 rest =>
    simp only [List.map_cons, List.length_map, List.length_cons, List.all_map,
      Function.comp_def]
    exact id

/-! ### Segments round-trip -/

theorem segOf_segLC (s : SegCmd) (hf : s.fits = true) : segOf (segLC s) = some s := by
  simp [segOf, segLC, decodeSeg_encodeSeg s hf]

theorem padded_length {P : Nat} (hP : 0 < P) (sg : Segment) :
    (sg.bytes ++ zeros (pad P sg.bytes.length)).length = chunkLen P sg.bytes.length := by
  simp [pad_add hP]

/-- A segment's command, read against a file that holds the segment's padded bytes at its offset,
gives back the padded segment. -/
theorem loadSeg_segCmdOf {P limit : Nat} (hP : 0 < P) (pre post : List UInt8) (sg : Segment)
    (hoff : pre.length % P = 0) (hlim : pre.length + chunkLen P sg.bytes.length ≤ limit)
    (h32 : limit < 2 ^ 32) :
    loadSeg P limit (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length)) ++ post)
      (segCmdOf P pre.length sg) = some (padSeg P sg) := by
  have hl := le_chunkLen hP sg.bytes.length
  have hsect : sectOk sg.perm sg.vaddr.toNat pre.length (chunkLen P sg.bytes.length)
      (encodeSect sg.perm sg.vaddr.toNat sg.bytes.length pre.length) = true :=
    sectOk_encodeSect _ (by omega) hl
  unfold loadSeg
  simp only [segCmdOf, permOf_protOf]
  rw [ite_eq_left ⟨protOf_lt _, trivial, trivial, trivial, trivial, hsect, hoff,
    chunkLen_mod _ _, hlim⟩]
  simp only [List.append_assoc, List.drop_left' rfl, UInt64.ofNat_toNat, padSeg]
  rw [← List.append_assoc, List.take_left' (padded_length hP sg)]

theorem blob_length_mod {P : Nat} (hP : 0 < P) : ∀ segs : List Segment,
    (blob P segs).length % P = 0
  | [] => rfl
  | sg :: sgs => by
    have := blob_length_mod hP sgs
    have h2 := chunkLen_mod P sg.bytes.length
    simp only [blob, List.length_append, zeros_length, pad_add hP]
    rw [Nat.add_mod, h2, this, Nat.zero_add, Nat.zero_mod]

theorem blob_cons (P : Nat) (sg : Segment) (sgs : List Segment) :
    blob P (sg :: sgs) = (sg.bytes ++ zeros (pad P sg.bytes.length)) ++ blob P sgs := by
  simp [blob]

/-- The commands that `layout` produces, read against a file that holds `blob` at their offset,
give back the padded segments. -/
theorem loadSegs_layout {P limit : Nat} (hP : 0 < P) (h32 : limit < 2 ^ 32) :
    ∀ (segs : List Segment) (pre post : List UInt8), pre.length % P = 0 →
    pre.length + (blob P segs).length ≤ limit → (layout P pre.length segs).all SegCmd.fits →
    loadSegs P limit (pre ++ blob P segs ++ post) ((layout P pre.length segs).map segLC) =
      some (segs.map (padSeg P))
  | [], _, _, _, _, _ => rfl
  | sg :: sgs, pre, post, hoff, hlim, hf => by
    simp only [layout, List.all_cons, Bool.and_eq_true] at hf
    rw [blob_cons, List.length_append, padded_length hP] at hlim
    have e : pre ++ blob P (sg :: sgs) ++ post =
        (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length))) ++ blob P sgs ++ post := by
      simp [blob]
    have hl : (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length))).length =
        pre.length + chunkLen P sg.bytes.length := by
      simp [padded_length hP]
    have hoff' : (pre ++ (sg.bytes ++ zeros (pad P sg.bytes.length))).length % P = 0 := by
      rw [hl, Nat.add_mod, hoff, chunkLen_mod, Nat.zero_mod]
    have ih := loadSegs_layout hP h32 sgs _ post hoff' (by rw [hl]; omega) (by rw [hl]; exact hf.2)
    rw [hl, ← e] at ih
    have h1 : loadSeg P limit (pre ++ blob P (sg :: sgs) ++ post) (segCmdOf P pre.length sg) =
        some (padSeg P sg) := by
      have := loadSeg_segCmdOf hP pre (blob P sgs ++ post) sg hoff (by omega) h32
      simpa [blob] using this
    simp only [layout, List.map_cons, loadSegs, segOf_segLC _ hf.1, Option.bind_eq_bind,
      Option.bind_some, h1, ih]

/-- `__TEXT` gives back the padded code segment. -/
theorem textSeg_textCmdOf {P limit : Nat} (hP : 0 < P) (pre post : List UInt8) (s0 : Segment)
    (hpre : pre.length = P) (hv : P ≤ s0.vaddr.toNat) (hend : s0.vaddr.toNat + s0.memSize < 2 ^ 64)
    (hlim : P + chunkLen P s0.bytes.length ≤ limit) (h32 : limit < 2 ^ 32) :
    textSeg P limit (pre ++ (s0.bytes ++ zeros (pad P s0.bytes.length)) ++ post)
      (textCmdOf P s0) = some (padSeg P s0) := by
  have e : ({ textCmdOf P s0 with
      vmaddr := (textCmdOf P s0).vmaddr + P, vmsize := (textCmdOf P s0).vmsize - P,
      fileoff := P, filesize := (textCmdOf P s0).filesize - P } : SegCmd) =
      segCmdOf P pre.length s0 := by
    simp only [textCmdOf, segCmdOf, hpre, SegCmd.mk.injEq]
    exact ⟨trivial, by omega, by omega, trivial, by omega, trivial, trivial, trivial, trivial,
      trivial⟩
  unfold textSeg
  rw [ite_eq_left ⟨rfl, by simp [textCmdOf], by simp [textCmdOf],
    by simp only [textCmdOf]; omega⟩, e]
  exact loadSeg_segCmdOf hP pre post s0 (by rw [hpre, Nat.mod_self]) (by rw [hpre]; exact hlim) h32

/-! ### How the loader model succeeds -/

/-- How `parse` succeeds, step by step. -/
theorem parse_of {c : Config} {pb : Nat} {st : UInt64} {bs : List UInt8} {n sz : Nat}
    {pz tx : Cmd} {rest : List Cmd} {t : SegCmd} {img : Image}
    (h0 : natOfBytes ((bs.drop 16).take 4) = n) (h0' : natOfBytes ((bs.drop 20).take 4) = sz)
    (h1 : bs.take HDR_SIZE = encodeHdr n sz)
    (h2 : decodeCmds n ((bs.drop HDR_SIZE).take sz) = some (pz :: tx :: rest))
    (h3 : pz = pageZeroCmd c) (h4 : segOf tx = some t) (h5 : parseCmds c (2 ^ pb) bs t rest = some img)
    (h6 : imageOk c pb st img = true) : parse c pb st bs = some img := by
  simp only [parse, h0, h0', h1, h2, h3, h4, h5, h6, ite_true]

/-- The conditions of `parseCmds` on the fixed commands. -/
structure TailOk (c : Config) (P : Nat) (bs : List UInt8) (t lk : SegCmd) (segs : List Segment)
    (di st ds dl uu bv mn lb cs : Cmd) : Prop where
  page : lk.fileoff % P = 0
  linkedit : lk = ⟨nLINKEDIT, lastEnd segs, bs.length - lk.fileoff, lk.fileoff,
    bs.length - lk.fileoff, 1, 1, 0, 0, []⟩
  dyldInfo : di = dyldInfoCmd
  symtab : st = symtabCmd lk.fileoff
  dysymtab : ds = dysymtabCmd
  dylinker : dl = dylinkerCmd
  uuid : uu.cmd = LC_UUID ∧ uu.body.length = 16
  build : bv = buildCmd
  main : mn = mainCmd (natOfBytes (mn.body.take 8)) (natOfBytes (mn.body.drop 8))
  entry : natOfBytes (mn.body.take 8) < t.vmsize
  dylib : lb = dylibCmd
  sig : cs = sigCmd (lk.fileoff + 16) (bs.length - (lk.fileoff + 16))
  pre : (bs.drop lk.fileoff).take 16 = linkeditPre
  sigBytes : bs.drop (lk.fileoff + 16) = codeSignature (bs.take (lk.fileoff + 16)) t.filesize

/-- How `parseCmds` succeeds. -/
theorem parseCmds_of {c : Config} {P : Nat} {bs : List UInt8} {t lk : SegCmd} {s0 : Segment}
    {sgs : List Segment} {mids : List Cmd} {le di st ds dl uu bv mn lb cs : Cmd}
    (h2 : segOf le = some lk) (h3 : textSeg P lk.fileoff bs t = some s0)
    (h4 : loadSegs P lk.fileoff bs mids = some sgs)
    (h5 : TailOk c P bs t lk (s0 :: sgs) di st ds dl uu bv mn lb cs) :
    parseCmds c P bs t (mids ++ [le, di, st, ds, dl, uu, bv, mn, lb, cs]) =
      some { segments := s0 :: sgs,
             entry := UInt64.ofNat (t.vmaddr + natOfBytes (mn.body.take 8)),
             stackSize := natOfBytes (mn.body.drop 8) - c.stackReserve } := by
  have hl : (mids ++ [le, di, st, ds, dl, uu, bv, mn, lb, cs]).length - 10 = mids.length := by
    simp
  unfold parseCmds
  rw [hl, List.drop_left' rfl, List.take_left' rfl]
  simp only [h2, h3, h4]
  rw [ite_eq_left ⟨h5.page, h5.linkedit, h5.dyldInfo, h5.symtab, h5.dysymtab, h5.dylinker,
    h5.uuid.1, h5.uuid.2, h5.build, h5.main, h5.entry, h5.dylib, h5.sig, h5.pre, h5.sigBytes⟩]

/-! ### Lengths and fields of the written file -/

theorem encodeCmds_append : ∀ (a b : List Cmd), encodeCmds (a ++ b) = encodeCmds a ++ encodeCmds b
  | [], _ => rfl
  | c :: a, b => by simp [encodeCmds, encodeCmds_append a b]

theorem hdr_split (n sz : Nat) (r : List UInt8) : encodeHdr n sz ++ r =
    (natBytes 4 MH_MAGIC_64 ++ natBytes 4 CPU_TYPE_ARM64 ++ natBytes 4 0 ++ natBytes 4 MH_EXECUTE) ++
      (natBytes 4 n ++ (natBytes 4 sz ++ (natBytes 4 MH_FLAGS ++ natBytes 4 0 ++ r))) := by
  simp [encodeHdr]

theorem hdr_ncmds (n sz : Nat) (r : List UInt8) (hn : n < 2 ^ 32) :
    natOfBytes (((encodeHdr n sz ++ r).drop 16).take 4) = n := by
  rw [hdr_split, List.drop_left' (by simp), List.take_left' (by simp), natOfBytes_natBytes,
    Nat.mod_eq_of_lt hn]

theorem hdr_sizeofcmds (n sz : Nat) (r : List UInt8) (hs : sz < 2 ^ 32) :
    natOfBytes (((encodeHdr n sz ++ r).drop 20).take 4) = sz := by
  rw [hdr_split, show 20 = 16 + 4 from rfl, ← List.drop_drop, List.drop_left' (by simp),
    List.drop_left' (by simp), List.take_left' (by simp), natOfBytes_natBytes,
    Nat.mod_eq_of_lt hs]

@[simp] theorem encodeSeg_length (s : SegCmd) :
    (encodeSeg s).length = s.name.length + 48 + s.sects.length := by
  simp [encodeSeg]; omega

theorem segCmdOf_name (P off : Nat) (sg : Segment) : (segCmdOf P off sg).name.length = 16 :=
  segName_length _

theorem segCmdOf_sects (P off : Nat) (sg : Segment) : (segCmdOf P off sg).sects.length = 80 :=
  encodeSect_length _ _ _ _

theorem cmdOk_segLC (s : SegCmd) (hn : s.name.length = 16) (hs : s.sects.length = 80) :
    cmdOk (segLC s) = true := by
  simp [cmdOk, segLC, hn, hs, LC_SEGMENT_64]

theorem layout_cmds (P : Nat) : ∀ (off : Nat) (segs : List Segment),
    ((layout P off segs).map segLC).all cmdOk = true ∧
      (encodeCmds ((layout P off segs).map segLC)).length = 152 * segs.length
  | _, [] => ⟨rfl, rfl⟩
  | off, sg :: sgs => by
    obtain ⟨h1, h2⟩ := layout_cmds P (off + chunkLen P sg.bytes.length) sgs
    simp only [layout, List.map_cons, List.all_cons, h1, Bool.and_true, encodeCmds,
      List.length_append, h2, encodeCmd_length, segLC, encodeSeg_length, segCmdOf_name,
      segCmdOf_sects, List.length_cons]
    refine ⟨cmdOk_segLC _ (segCmdOf_name _ _ _) (segCmdOf_sects _ _ _), by omega⟩

@[simp] theorem layout_length (P : Nat) : ∀ (off : Nat) (segs : List Segment),
    (layout P off segs).length = segs.length
  | _, [] => rfl
  | _, _ :: sgs => by simp [layout, layout_length P _ sgs]

theorem cmdsOf_facts (c : Config) (P : Nat) (img : Image) (s0 : Segment) (rest : List Segment) :
    (cmdsOf c P img s0 rest).all cmdOk = true ∧
      (encodeCmds (cmdsOf c P img s0 rest)).length = 152 * rest.length + 624 ∧
      (cmdsOf c P img s0 rest).length = rest.length + 12 := by
  obtain ⟨h1, h2⟩ := layout_cmds P (P + chunkLen P s0.bytes.length) rest
  simp only [cmdsOf, List.all_cons, List.all_append, h1, encodeCmds, encodeCmds_append,
    List.length_append, h2, List.length_cons, List.length_map, layout_length]
  refine ⟨?_, ?_, by simp⟩
  · simp [cmdOk, segLC, textCmdOf, segCmdOf_name, segCmdOf_sects, pageZeroCmd, linkeditSeg,
      dyldInfoCmd, symtabCmd, dysymtabCmd, dylinkerCmd, buildCmd, mainCmd, dylibCmd, sigCmd,
      LC_SEGMENT_64, LC_DYLD_INFO_ONLY, LC_SYMTAB, LC_DYSYMTAB, LC_LOAD_DYLINKER, LC_UUID,
      LC_BUILD_VERSION, LC_MAIN, LC_LOAD_DYLIB, LC_CODE_SIGNATURE, nPAGEZERO, nLINKEDIT, cstr]
  · simp [segLC, textCmdOf, segCmdOf_name, segCmdOf_sects, pageZeroCmd, linkeditSeg,
      dyldInfoCmd, symtabCmd, dysymtabCmd, dylinkerCmd, buildCmd, mainCmd, dylibCmd, sigCmd,
      nPAGEZERO, nLINKEDIT, cstr]
    omega

theorem mainCmd_fields (e st : Nat) (he : e < 2 ^ 64) (hs : st < 2 ^ 64) :
    natOfBytes ((mainCmd e st).body.take 8) = e ∧ natOfBytes ((mainCmd e st).body.drop 8) = st := by
  simp only [mainCmd, List.take_left' (natBytes_length _ _), List.drop_left' (natBytes_length _ _),
    natOfBytes_natBytes, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hs, and_self]

/-! ### The round trip -/

/-- `write` succeeds only on a checked image whose fields fit, and then returns `fileBytes`. -/
theorem write_inv {c : Config} {pb : Nat} {st : UInt64} {img : Image} {bs : List UInt8}
    (h : write c pb st img = .ok bs) :
    imageOk c pb st img = true ∧ fitsOk c (2 ^ pb) img = true ∧
      bs.length < 2 ^ 32 ∧ bs = fileBytes c (2 ^ pb) img := by
  unfold write at h; grind

/-- The facts of `imageOk` about the first segment. -/
theorem imageOk_cons {c : Config} {pb : Nat} {st : UInt64} {img : Image} {s0 : Segment}
    {rest : List Segment} (h : imageOk c pb st img = true) (hs : img.segments = s0 :: rest) :
    c.pageZero + 2 ^ pb ≤ s0.vaddr.toNat ∧ s0.vaddr.toNat ≤ img.entry.toNat ∧
      img.entry.toNat < s0.vaddr.toNat + s0.memSize ∧ headerSize (rest.length + 1) ≤ 2 ^ pb := by
  simp only [imageOk, hs, Bool.and_eq_true, decide_eq_true_eq, List.length_cons] at h
  exact ⟨h.1.1.1.1.2.1.1.1.2, h.1.1.1.1.2.1.1.2, h.1.1.1.1.2.1.2, h.2⟩

theorem fitsOk_cons {c : Config} {P : Nat} {img : Image} {s0 : Segment} {rest : List Segment}
    (h : fitsOk c P img = true) (hs : img.segments = s0 :: rest) :
    (textCmdOf P s0).fits = true ∧
      (layout P (P + chunkLen P s0.bytes.length) rest).all SegCmd.fits = true ∧
      s0.vaddr.toNat + s0.memSize < 2 ^ 64 ∧ lastEnd img.segments < 2 ^ 64 ∧
      img.stackSize + c.stackReserve < 2 ^ 64 := by
  simp only [fitsOk, hs, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hs]
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The layout of the written file: the header page, the code's pages, the other segments'
pages, the start of `__LINKEDIT`, and the signature of everything before it. -/
theorem file_layout {c : Config} {P : Nat} {img : Image} {s0 : Segment} {rest : List Segment}
    (hP : 0 < P) (hs : img.segments = s0 :: rest)
    (hhdr : headerSize (rest.length + 1) ≤ P) :
    (hdrBytes c P img s0 rest).length = headerSize (rest.length + 1) ∧
    unsigned c P img s0 rest = (hdrBytes c P img s0 rest ++
        zeros (P - (hdrBytes c P img s0 rest).length)) ++
      (s0.bytes ++ zeros (pad P s0.bytes.length)) ++ blob P rest ++ linkeditPre ∧
    linkOff P img = P + chunkLen P s0.bytes.length + (blob P rest).length ∧
    (unsigned c P img s0 rest).length = linkOff P img + 16 ∧
    fileBytes c P img = unsigned c P img s0 rest ++
      codeSignature (unsigned c P img s0 rest) (P + chunkLen P s0.bytes.length) := by
  obtain ⟨_, hclen, _⟩ := cmdsOf_facts c P img s0 rest
  have hblob : blob P img.segments = (s0.bytes ++ zeros (pad P s0.bytes.length)) ++ blob P rest := by
    rw [hs, blob_cons]
  have hH : (hdrBytes c P img s0 rest).length = headerSize (rest.length + 1) := by
    simp only [hdrBytes, List.length_append, encodeHdr_length, hclen, headerSize, HDR_SIZE]
    omega
  have hL : linkOff P img = P + chunkLen P s0.bytes.length + (blob P rest).length := by
    simp only [linkOff, hblob, List.length_append, padded_length hP]; omega
  refine ⟨hH, by simp only [unsigned, hblob, List.append_assoc], hL, ?_,
    by simp only [fileBytes, hs]⟩
  simp only [unsigned, hblob, List.length_append, zeros_length, padded_length hP, hL]
  simp only [linkeditPre, List.length_cons, zeros_length]
  omega

/-- The fixed commands and `__LINKEDIT` of a written file pass the loader model's checks. -/
theorem tailOk_write {c : Config} {pb : Nat} {st : UInt64} {img : Image} {s0 : Segment}
    {rest : List Segment} (hok : imageOk c pb st img = true) (hfit : fitsOk c (2 ^ pb) img = true)
    (hs : img.segments = s0 :: rest) :
    TailOk c (2 ^ pb) (fileBytes c (2 ^ pb) img) (textCmdOf (2 ^ pb) s0)
      (linkeditSeg (lastEnd img.segments) (linkOff (2 ^ pb) img)
        (16 + sigSize (linkOff (2 ^ pb) img + 16)))
      (padSeg (2 ^ pb) s0 :: rest.map (padSeg (2 ^ pb))) dyldInfoCmd
      (symtabCmd (linkOff (2 ^ pb) img)) dysymtabCmd dylinkerCmd
      ⟨LC_UUID, (Sha256.hash (blob (2 ^ pb) img.segments)).take 16⟩ buildCmd
      (mainCmd (img.entry.toNat - (s0.vaddr.toNat - 2 ^ pb)) (img.stackSize + c.stackReserve))
      dylibCmd (sigCmd (linkOff (2 ^ pb) img + 16) (sigSize (linkOff (2 ^ pb) img + 16))) := by
  have hP : 0 < 2 ^ pb := Nat.two_pow_pos pb
  obtain ⟨hv0, hve, hen, hhdr⟩ := imageOk_cons hok hs
  obtain ⟨_, _, _, _, fstack⟩ := fitsOk_cons hfit hs
  obtain ⟨hH, hu, hL, hulen, hbs⟩ := file_layout (c := c) hP hs hhdr
  generalize unsigned c (2 ^ pb) img s0 rest = u at hu hulen hbs
  generalize linkOff (2 ^ pb) img = L at hL hulen ⊢
  have hbl : (fileBytes c (2 ^ pb) img).length = L + 16 + sigSize (L + 16) := by
    rw [hbs, List.length_append, codeSignature_length, hulen]
  have hmain := mainCmd_fields (img.entry.toNat - (s0.vaddr.toNat - 2 ^ pb))
    (img.stackSize + c.stackReserve) (by have := img.entry.toNat_lt; omega) fstack
  have hpreL : (fileBytes c (2 ^ pb) img).drop L = linkeditPre ++
      codeSignature u (2 ^ pb + chunkLen (2 ^ pb) s0.bytes.length) := by
    rw [hbs]
    generalize codeSignature u _ = sg
    have e : u ++ sg =
        ((hdrBytes c (2 ^ pb) img s0 rest ++ zeros (2 ^ pb - (hdrBytes c (2 ^ pb) img s0 rest).length)) ++
          (s0.bytes ++ zeros (pad (2 ^ pb) s0.bytes.length)) ++ blob (2 ^ pb) rest) ++
        (linkeditPre ++ sg) := by
      rw [hu]; simp only [List.append_assoc]
    rw [e, List.drop_left' (by
      simp only [List.length_append, zeros_length, padded_length hP, hH, hL]; omega)]
  have hpage : L % 2 ^ pb = 0 := by
    rw [hL, Nat.add_mod, Nat.add_mod (2 ^ pb), Nat.mod_self, chunkLen_mod,
      blob_length_mod hP]
    simp
  exact {
    page := hpage
    linkedit := by
      have he : lastEnd (padSeg (2 ^ pb) s0 :: rest.map (padSeg (2 ^ pb))) = lastEnd img.segments := by
        rw [hs, ← lastEnd_pad (2 ^ pb) (s0 :: rest), List.map_cons]
      simp only [linkeditSeg, he, hbl, SegCmd.mk.injEq, true_and, and_true]
      omega
    dyldInfo := rfl
    symtab := rfl
    dysymtab := rfl
    dylinker := rfl
    uuid := ⟨rfl, by simp⟩
    build := rfl
    main := by rw [hmain.1, hmain.2]
    entry := by rw [hmain.1]; simp only [textCmdOf]; omega
    dylib := rfl
    sig := by
      simp only [linkeditSeg, hbl]
      rw [show L + 16 + sigSize (L + 16) - (L + 16) = sigSize (L + 16) by omega]
    pre := by
      simp only [linkeditSeg]
      rw [hpreL, List.take_left' (show linkeditPre.length = 16 from rfl)]
    sigBytes := by
      simp only [linkeditSeg, textCmdOf]
      rw [hbs, ← hulen, List.drop_left' rfl, List.take_left' rfl] }

/-- The loader model parses what the writer wrote into the image the writer was given, with each
segment's bytes padded to whole pages. -/
theorem parse_write {c : Config} {pb : Nat} {st : UInt64} {img : Image} {bs : List UInt8}
    (h : write c pb st img = .ok bs) : parse c pb st bs = some (padImage (2 ^ pb) img) := by
  obtain ⟨hok, hfit, hlen, rfl⟩ := write_inv h
  have hP : 0 < 2 ^ pb := Nat.two_pow_pos pb
  obtain ⟨s0, rest, hs⟩ : ∃ s0 rest, img.segments = s0 :: rest := by
    cases h' : img.segments with
    | nil => simp [fitsOk, h'] at hfit
    | cons s0 rest => exact ⟨s0, rest, rfl⟩
  obtain ⟨hv0, hve, hen, hhdr⟩ := imageOk_cons hok hs
  obtain ⟨ftx, flay, fend, _, fstack⟩ := fitsOk_cons hfit hs
  obtain ⟨hcok, hclen, hcn⟩ := cmdsOf_facts c (2 ^ pb) img s0 rest
  obtain ⟨hH, hu, hL, hulen, hbs⟩ := file_layout (c := c) hP hs hhdr
  have htail := tailOk_write hok hfit hs
  have hmain := mainCmd_fields (img.entry.toNat - (s0.vaddr.toNat - 2 ^ pb))
    (img.stackSize + c.stackReserve) (by have := img.entry.toNat_lt; omega) fstack
  -- the file as header, commands, header-page padding, segments and the rest
  let cmds := cmdsOf c (2 ^ pb) img s0 rest
  let pre := hdrBytes c (2 ^ pb) img s0 rest ++
    zeros (2 ^ pb - (hdrBytes c (2 ^ pb) img s0 rest).length)
  let pad0 := s0.bytes ++ zeros (pad (2 ^ pb) s0.bytes.length)
  obtain ⟨sig, hsig⟩ : ∃ sig, sig = codeSignature (unsigned c (2 ^ pb) img s0 rest)
    (2 ^ pb + chunkLen (2 ^ pb) s0.bytes.length) := ⟨_, rfl⟩
  rw [← hsig] at hbs
  have hpre : pre.length = 2 ^ pb := by simp only [pre, List.length_append, zeros_length, hH]; omega
  have hsplit : fileBytes c (2 ^ pb) img = pre ++ pad0 ++ (blob (2 ^ pb) rest ++ linkeditPre ++ sig) := by
    rw [hbs, hu]; simp only [pre, pad0, List.append_assoc]
  have hX : fileBytes c (2 ^ pb) img = encodeHdr cmds.length (encodeCmds cmds).length ++
      (encodeCmds cmds ++ (zeros (2 ^ pb - (hdrBytes c (2 ^ pb) img s0 rest).length) ++ pad0 ++
        blob (2 ^ pb) rest ++ linkeditPre ++ sig)) := by
    rw [hbs, hu]; simp only [hdrBytes, cmds, pad0, List.append_assoc]
  have hClt : (encodeCmds cmds).length < 2 ^ 32 := by
    have := congrArg List.length hX
    simp only [List.length_append] at this; omega
  have hnlt : cmds.length < 2 ^ 32 := by
    have : cmds.length = rest.length + 12 := hcn
    rw [this]; rw [hclen] at hClt; omega
  -- the segments
  have hLlen : linkOff (2 ^ pb) img + 16 < 2 ^ 32 := by
    have := congrArg List.length hbs
    simp only [List.length_append, hulen] at this; omega
  have htext : textSeg (2 ^ pb) (linkOff (2 ^ pb) img) (fileBytes c (2 ^ pb) img)
      (textCmdOf (2 ^ pb) s0) = some (padSeg (2 ^ pb) s0) := by
    rw [hsplit]
    exact textSeg_textCmdOf hP pre _ s0 hpre (by omega) fend (by omega) (by omega)
  have hpp : (pre ++ pad0).length = 2 ^ pb + chunkLen (2 ^ pb) s0.bytes.length := by
    simp only [List.length_append, hpre, pad0, padded_length hP]
  have hmids : loadSegs (2 ^ pb) (linkOff (2 ^ pb) img) (fileBytes c (2 ^ pb) img)
      ((layout (2 ^ pb) (2 ^ pb + chunkLen (2 ^ pb) s0.bytes.length) rest).map segLC) =
      some (rest.map (padSeg (2 ^ pb))) := by
    have e : fileBytes c (2 ^ pb) img =
        (pre ++ pad0) ++ blob (2 ^ pb) rest ++ (linkeditPre ++ sig) := by
      rw [hsplit]; simp only [List.append_assoc]
    rw [e, ← hpp]
    refine loadSegs_layout hP (by omega) rest _ _ ?_ (by rw [hpp]; omega) (by rw [hpp]; exact flay)
    rw [hpp, Nat.add_mod, Nat.mod_self, chunkLen_mod, Nat.zero_add, Nat.zero_mod]
  -- the linkedit command and the image read back
  have hlk : segOf (segLC (linkeditSeg (lastEnd img.segments) (linkOff (2 ^ pb) img)
      (16 + sigSize (linkOff (2 ^ pb) img + 16)))) =
      some (linkeditSeg (lastEnd img.segments) (linkOff (2 ^ pb) img)
        (16 + sigSize (linkOff (2 ^ pb) img + 16))) := by
    obtain ⟨_, _, _, flast, _⟩ := fitsOk_cons hfit hs
    have := congrArg List.length hbs
    simp only [List.length_append, hsig, codeSignature_length, hulen] at this
    refine segOf_segLC _ ?_
    simp only [SegCmd.fits, linkeditSeg, Bool.and_eq_true, beq_iff_eq, fits_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨rfl, flast⟩, by omega⟩, by omega⟩, by omega⟩, by decide⟩, by decide⟩,
      by decide⟩, by decide⟩
  have h5 := parseCmds_of hlk htext hmids htail
  have himg : ({
      segments := padSeg (2 ^ pb) s0 :: rest.map (padSeg (2 ^ pb)),
      entry := UInt64.ofNat ((textCmdOf (2 ^ pb) s0).vmaddr + natOfBytes ((mainCmd
        (img.entry.toNat - (s0.vaddr.toNat - 2 ^ pb)) (img.stackSize + c.stackReserve)).body.take 8)),
      stackSize := natOfBytes ((mainCmd (img.entry.toNat - (s0.vaddr.toNat - 2 ^ pb))
        (img.stackSize + c.stackReserve)).body.drop 8) - c.stackReserve } : Image) =
      padImage (2 ^ pb) img := by
    rw [hmain.1, hmain.2]
    simp only [padImage, hs, List.map_cons, Image.mk.injEq, true_and, Nat.add_sub_cancel]
    refine ⟨?_, trivial⟩
    rw [show (textCmdOf (2 ^ pb) s0).vmaddr + (img.entry.toNat - (s0.vaddr.toNat - 2 ^ pb)) =
      img.entry.toNat by simp only [textCmdOf]; omega, UInt64.ofNat_toNat]
  rw [himg] at h5
  -- the header and the commands
  have h2 : decodeCmds cmds.length
      (((fileBytes c (2 ^ pb) img).drop HDR_SIZE).take (encodeCmds cmds).length) = some cmds := by
    rw [hX, List.drop_left' (encodeHdr_length _ _), List.take_left' rfl]
    exact decodeCmds_encodeCmds cmds hcok
  refine parse_of (by rw [hX]; exact hdr_ncmds _ _ _ hnlt)
    (by rw [hX]; exact hdr_sizeofcmds _ _ _ hClt)
    (by rw [hX, List.take_left' (encodeHdr_length _ _)]) h2 rfl (segOf_segLC _ ftx) h5
    (imageOk_pad hok)

/-- Loading what the Mach-O writer produced gives exactly the image's initial machine state. -/
theorem load_write {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    (h : write c abi.pageBits abi.stackTop img = .ok bs) : load c abi bs = some (img.init abi) := by
  simp [load, parse_write h, init_padImage]

theorem imageOk_valid {c : Config} {pb : Nat} {st : UInt64} {img : Image}
    (h : imageOk c pb st img = true) : validAt pb st img = true := by
  simp only [imageOk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

/-- The writer refuses invalid images. -/
theorem write_valid {c : Config} {isa : Isa} {abi : Abi isa} {img : Image} {bs : List UInt8}
    (h : write c abi.pageBits abi.stackTop img = .ok bs) : img.valid abi = true := by
  rw [Elf.valid_eq]; exact imageOk_valid (write_inv h).1

/-! ### The `Format` value -/

/-- The Mach-O format for an ABI, under the OS facts `c`. -/
def format (c : Config) {isa : Isa} (abi : Abi isa) : Format isa abi where
  write := write c abi.pageBits abi.stackTop
  load := load c abi

/-- The Mach-O format satisfies the format laws. -/
theorem laws (c : Config) {isa : Isa} (abi : Abi isa) : (format c abi).Laws where
  write_valid _ _ h := write_valid h
  load_write _ _ h := load_write h

/-- Mach-O for arm64 macOS. -/
def a64Macos {isa : Isa} (abi : Abi isa) : Format isa abi := format Config.a64Macos abi

theorem a64Macos_laws {isa : Isa} (abi : Abi isa) : (a64Macos abi).Laws := laws _ abi

/-! ### Accepted files: memory is W^X -/

/-- Whatever the loader model accepts passes the image check. -/
theorem parse_imageOk {c : Config} {pb : Nat} {st : UInt64} {bs : List UInt8} {img : Image}
    (h : parse c pb st bs = some img) : imageOk c pb st img = true := by
  unfold parse at h
  simp only at h
  repeat' split at h
  all_goals first | (cases h; done) | (cases h; assumption)

/-- Any file the loader model accepts starts in W^X memory. -/
theorem load_wxorx {c : Config} {isa : Isa} {abi : Abi isa} {bs : List UInt8}
    {s : MState isa.Regs} (h : load c abi bs = some s) : s.mem.WxorX := by
  unfold load at h
  cases hp : parse c abi.pageBits abi.stackTop bs with
  | none => rw [hp] at h; cases h
  | some img =>
    rw [hp] at h; cases h
    exact Image.init_wxorx abi img (by rw [Elf.valid_eq]; exact imageOk_valid (parse_imageOk hp))

end Millipede.MachO
