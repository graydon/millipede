import Millipede.Object.Image

/-!
# Object formats and loader models

A `Format isa abi` is a writer from `Image` to bytes together with a loader model, a Lean function
that describes what the operating system does with the file. The loader model parses the headers,
maps the segments, fills with zeros, sets permissions and sets the entry state. It is part of the
trusted base, since it is the specification of `execve`. Bytes are `List UInt8` in the model, and
the driver converts them to a `ByteArray` only to write the file.

Each format proves its `Format.Laws`. `write_valid` says that the writer refuses images that fail
`Image.valid`, so segments do not overlap, are W^X and lie below the stack. `load_write` says that
loading what was written gives exactly the image's initial machine state. ELF cannot express the
stack size, since Linux takes it from `RLIMIT_STACK`, so the loader model's stack is a modelling
assumption that the ledger records.
-/

namespace Millipede

/-- An executable format with its loader model, for one ISA and ABI. -/
structure Format (isa : Isa) (abi : Abi isa) where
  /-- serialises an image, refusing images that it cannot represent -/
  write : Image → Except String (List UInt8)
  /-- the loader model, which gives the state in which the operating system starts the process,
  or `none` when it refuses the file -/
  load : List UInt8 → Option (MState isa.Regs)

/-- The laws of a format. -/
structure Format.Laws {isa : Isa} {abi : Abi isa} (fmt : Format isa abi) : Prop where
  write_valid : ∀ img bs, fmt.write img = .ok bs → img.valid abi = true
  load_write : ∀ img bs, fmt.write img = .ok bs → fmt.load bs = some (img.init abi)

end Millipede
