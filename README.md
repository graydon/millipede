# Millipede

## LLM notice

Most of this repo is written by an LLM. If this offends, close the tab and move on.

This readme is written by a human.

## Overview

This is an experiment in trying to answer the question "what should programming languages look like in the LLM era?" Meaning: a time when LLMs are the target program-writing audience, and also the threat model, and also the language implementers. 

Some characteristics:

- Low level, imperative, linear typed with borrows, no panic or UB
- Lots of extra fiddly typing disciplines
    - Finite time & space bounds, no heap
    - Interface/implementation split, with contracts and specs
    - Typestates, session types, unit checking, information flow control, etc. etc.
- Implemented as a deep [embedded DSL](doc/design/embedding.md) in Lean 4
    - Each definition [elaborated](Millipede/Meta/Elab.lean) to a [Core](Millipede/Core/Exp.lean) term and a related Lean function (and some other stuff)
    - Core term [denotation](Millipede/Core/Denote.lean) then auto-proved extensionally equal to Lean function
    - Lean used for specifying and proving correctness properties of either object (vcgen, grind, etc.)
    - Lean used for anything higher order or polymorphic
    - Core term used for the algorithmic, monomorphic inner programs
    - Proofs about space, time, linearity etc. use Core term
    - Core term compiled independently of normal Lean compilation path
- [Verified compilation](Millipede/Top/Compile.lean) through a sequence of [lowerings](Millipede/Compile/Lower.lean) with [memory refinement](Millipede/Compile/LowerSound.lean) and [forward simulation proofs](Millipede/Compile/Sem.lean) relating each layer's semantics. The compiler is written as a Lean function from Core terms to loadable OS object-file bytes: no LLVM or host toolchains are involved.

## Ignorance caveat

**I cannot say with high confidence how close to reality any of the above characteristics are.**

This repo wasn't just written by an LLM to save time, but also because I literally couldn't have written it myself. Most of the theorems much less proofs are over my head. I'm trying to understand what is here, and part of this exploration is the question of how to relate to work I'm _guiding_ while not fully understanding what it's doing. I expect this phenomenon to get worse.

I am not providing this as a suggestion for anyone to rush out and use (it's slow and generates bad code) or even necessarily spend any of their precious time on earth trying to review for correctness. It's an exploratory project, a provocation to other PL people who know this landscape better than me to try something similar, and mainly just a concrete answer to a question I keep getting asked.

## Navigation

### Implementation

- Design docs: [doc/design/README.md](doc/design/README.md)
- Codebase & theorem tour: [doc/guide/tour.md](doc/guide/tour.md)
- Status of work and claims: [doc/status.md](doc/status.md)
- Roadmap: [doc/roadmap.md](doc/roadmap.md)

### Language

- Language surface reference: [doc/reference/surface.md](doc/reference/surface.md)
- Language tutorial: [doc/guide/tutorial.md](doc/guide/tutorial.md)

Note: the tutorial is messy, and the worked example quite trivial. The language is mostly meaningful in terms of its restrictions and missing features; there's nothing exciting about it from an expressivity perspective. I wouldn't bother reading it unless you're morbidly curious, it reads mostly like Lean do-notation with some Rust-isms thrown in. Humans aren't the target audience for writing Millipede programs anyways.

If you're just wondering what it looks like, here's a snippet from the library:

```lean
mp def ByteBuf.readFrom (b : &mut ByteBuf cap) (fd : UInt64)
    requires ByteBuf.Inv cap b
    ensures ByteBuf.Inv cap b' : UInt64
:=
do
  let n := b.len
  let r := ByteBuf.sysRead fd (&mut b.bytes[n..cap])
  if r <= cap -! n then
    b.len := n +! r
    r
  else r
```

There should really be nothing surprising in the language.

## Prior art

[Tons](doc/design/prior-art.md). There's really nothing new here besides:

  - LLM attackers increasing the urgency of adopting more rigorous techniques.
  - LLM programmers reducing the cost of adopting those techniques, including proof-writing.
  - LLM compiler-writers reducing the cost of proving the compilers themselves correct.

When costs change, it can change which techniques make sense.

## Cost and complexity

Writing this used 1 week of Fable 5.2 time driving mostly Opus 5.5 agents driving Lean on a macbook air M4 laptop.

As a quarter-month worth of a USD $200/mo "ultra" subscription -- 100% of weekly quota was used -- it feels fair to call it USD $50 of compute. Plus or minus whatever arithmetic you apply to Anthropic's subsidized subscription rates.

Human supervision / intervention time was about 6 hours total. Mostly I just checked in at the beginning and end of each day.

The codebase weighs in at roughly:
  - 60kloc of Lean
    - 2000-ish definitions
    - 3000-ish theorems
  - 13kloc of comments
  - 15kloc of tests
