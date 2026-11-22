# Measurements

Current figures only (the one home of the figures).

How they are produced: `scripts/measure.sh` (static: instruction lines of the executable segment
of the ELF, by `x64-objdump`; dynamic: instructions executed under `qemu-x86_64
-one-insn-per-tb -d exec`), `scripts/proof-burden.sh` (the classifier of `#mp_report`,
Millipede/Meta/Burden.lean), `scripts/census.lean` (safety proofs; usage in its header), and
`scripts/kappa.lean` (checks and searches the `X64.κ` and `A64.κ` weights). The programs measured are the `mpc` instances
(`Examples.registry`, Millipede/Top/Examples.lean), the differential suite's one-case harnesses
(Tests/Differential/) and the cost programs.

## Generated code and instruction counts

**Generated code.** Images are byte-identical across the reviews that followed the merged phase 3.
The instruction counts (static and dynamic) were last measured at the end of phase 2f. The cost models
(what each weight pays for: design/resources.md):
`X64.κ` word 32, iter 64, loop 16, prim 36, div 46, mem 28, place 5, ref 40, call 15, ext 18,
ite 11, ctor 14, atom 5, let 4, match 0; `A64.κ` word 29, iter 59, loop 13, prim 36, div 37,
mem 27, place 5, ref 39, call 18, ext 19, ite 10, ctor 9, atom 5, let 3, match 0. Neither refuses
any program of scripts/kappa.lean (4,536 compilations each: every program, pass configuration and
register-allocation setting).

## Bounds against measured runs

`BOUND_PROGRAMS="exit42 hello sum ticks readcount pooltally revchunks reqspool reqsbump"
scripts/bound-check.sh` (2026-11-19) runs each registered program under qemu on a 40-byte input:
the step bound `p.stepCost` (per target) against the largest step (the most instructions between
the last events of two consecutive reactor steps), and the deepest stack against `p.stackBytes`
and the image's request (`PT_GNU_STACK`). In brackets, the ratio at the previous weights.

| program | step bound x64 / arm64 | largest step x64 / arm64 | ratio (before) | stack x64 / arm64 | `p.stackBytes` ratio | image's request x64 / arm64 | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|
| ticks | 132 / 127 | 78 / 66 | 1.7 / 1.9 (2.2 / 2.6) | 24 / 32 | 13 / 10 | 32 / 32 | 1.3 / 1.0 |
| readcount | 132 / 127 | 77 / 59 | 1.7 / 2.2 (2.3 / 2.9) | 56 / 64 | 5.6 / 5.0 | 64 / 64 | 1.1 / 1.0 |
| pooltally | 6,119 / 5,747 | 1,180 / 959 | 5.2 / 6.0 (5.8 / 7.2) | 232 / 256 | 44 / 52 | 240 / 256 | 1.0 / 1.0 |
| revchunks | 10,060 / 9,365 | 1,304 / 1,088 | 7.7 / 8.6 (7.4 / 8.9) | 120 / 144 | 50 / 42 | 128 / 144 | 1.1 / 1.0 |
| reqspool | 17,320 / 16,200 | 2,431 / 2,011 | 7.1 / 8.1 (8.7 / 10.4) | 224 / 240 | 33 / 31 | 232 / 240 | 1.0 / 1.0 |
| reqsbump | 4,307 / 3,985 | 1,413 / 1,172 | 3.0 / 3.4 (5.4 / 6.4) | 168 / 192 | 34 / 30 | 176 / 192 | 1.0 / 1.0 |

`exit42`, `hello` and `sum` finish in `init` (bounds 27, 49, 2,265 against 5, 18, 194 on x64).
scripts/step-measure.py (most instructions between two `read`s or two `write`s): the audit's
`upper` (64-byte buffer, on 4 KiB of random lower-case text) and `kvsrv` (Tests/FormatKVSrv.lean,
five `put`s of 32-byte values and five `get`s):

| program | step bound x64 / arm64 (before) | largest step x64 / arm64 | ratio (before) | stack x64 / arm64 | `p.stackBytes` | image's request x64 / arm64 |
|---|---:|---:|---:|---:|---:|---:|
| upper | 88,022 / 83,867 (71,004) | 5,946 / 4,908 | 15 / 17 (12 / 14) | 136 / 160 | 25,384 | 144 / 160 |
| kvsrv | 110,465 / 102,660 (129,703) | 9,810 / 7,849 | 11 / 13 (13 / 17) | 256 / 304 | 321,888 | 264 / 304 |

What separates the bounds from the runs: every loop is charged its full count (`upper`'s write
loop 64 times, run once), a branch its dearer arm, a byte array one word per byte, and each
weight is the worst case of its construct over every register-allocation setting, which for a
primitive is two operands read through references with allocation off (32 instructions on x64,
against 4 with both in registers); `upper` runs 1,348 primitives a step.

## Against gcc

The audit's programs and two of the registry's, written in C (`gcc -O2 -nostdlib -static -s`,
arm64, a direct `svc` loop), on this host. The outputs
are identical. Code is the executable segment without its trailing zeros; for gcc it is `.text`.
Executed instructions are qemu's count. "S6 step 3" adds data-region
addressing, x64 immediates and identity operations as moves (phase-4b-regalloc.md, S5, S6).

| program, input | file x64 / arm64 / gcc | code x64 / arm64 / gcc | executed x64 / arm64 / gcc |
|---|---:|---:|---:|
| upper, 64 KiB, audit | 8,192 / 131,072 / 1,184 | 2,831 / 1,688 / 244 | 4,390,771 / 3,521,845 / 626,305 |
| upper, S6 step 3 | 8,192 / 131,072 | 1,869 / 1,128 | 2,810,704 (4.5×) / 2,203,432 (3.5×) |
| upper with a 64 KiB buffer, audit | 8,192 / 131,072 / 1,184 | 2,889 / 1,792 / 244 | 4,374,438 / 3,577,245 / 596,638 |
| revchunks, 4 KiB, audit | 8,192 / 131,072 / 1,096 | 2,775 / 1,600 / 156 | 334,027 / 278,685 / 21,262 |
| revchunks, S6 step 3 | 8,192 / 131,072 | 1,549 / 904 | 171,094 (8.0×) / 141,911 (6.7×) |
| kvsrv, 244 bytes, audit | 61,440 / 131,072 / 2,040 | 53,610 / 31,376 / 1,032 | 98,662 / 79,850 / 2,494 |
| kvsrv, S6 step 3 | 36,864 / 131,072 | 29,607 / 16,548 | 52,231 (21×) / 45,828 (18×) |
| frame, 3,000 bytes, audit | 16,384 / 196,608 / 2,176 | 6,562 / 3,768 / 296 | 955,580 / 767,968 / 56,603 |

A data load or store is two instructions on x64 (`lea r11, [rip + mp_mem]`, `[r11 + a + off]`)
and one or two on arm64 (`[x29, a]`, or `add x16, a, #off; [x29, x16]`); x64 stores immediates and
uses 32-bit ALU immediates directly; `bor x, x, 0` and `mul i, i, 1` select to no code. arm64
files are at least 128 KiB because the loader model lays out 64 KiB pages.

## Register allocation (phase 4b)

**Caller-saved locations (S4).** `compile` adds 3 caller-saved register locations on x64 (`r8 r9 r10`) and 9 on arm64 (`x4…x7, x10…x14`), and the allocator tries the preserved ones first. Static and executed instructions against the previous main, with `hpLeaf` and `hpCall` the two high-pressure functions of Tests/Differential/Funcs.lean:

| | static mpc / harnesses | `s:ops6` / extra / `l:ops6` | stack | mpc text | `hpLeaf` / `hpCall` executed |
|---|---|---|---|---|---|
| x64, previous main | 3,907 / 42,239 | 14,777 / 5,685 / 79,401 | 5,816 | 17,923 | 531,100 / 557,635 |
| x64, `c = 3`, preserved first (`compile`) | 3,889 / 42,169 (−0.5% / −0.2%) | 14,731 / 5,639 / 79,115 (−0.3% / −0.8% / −0.4%) | 7,312 (+26%) | 17,841 (−0.5%) | 521,869 / 543,517 (−1.7% / −2.5%) |
| arm64, previous main | 2,591 / 24,166 | 11,714 / 4,685 / 60,938 | 5,856 | 10,364 | 432,269 / 459,782 |
| arm64, `c = 9`, preserved first (`compile`) | 2,579 / 24,133 (−0.5% / −0.1%) | 11,668 / 4,639 / 60,652 (−0.4% / −1.0% / −0.5%) | 10,896 (+86%) | 10,316 (−0.5%) | 399,146 / 441,863 (−7.7% / −3.9%) |

Preserved first executes fewer instructions on the two high-pressure functions together, so it is the default (the `callerFirst` option of `compile`).

The stack each image asks for (its `PT_GNU_STACK` size), summed by `scripts/measure.sh hpLeaf hpCall` over the 34 differential harnesses and the 7 `mpc` instances it builds, is the same as before S4 on arm64 and 16 bytes smaller on x64:

| | harnesses | `mpc` instances | `reqspool` / `reqsbump` |
|---|---:|---:|---:|
| x64 before S4 / S4 / now | 6,280 / 7,872 / 6,264 | 536 / 584 / 536 | 216, 160 / 240, 184 / 216, 160 |
| arm64 before S4 / S4 / now | 6,336 / 11,696 / 6,336 | 592 / 752 / 592 | 224, 176 / 304, 256 / 224, 176 |

**Parallel moves for results and system-call arguments (2026-11-20).** `ret`, the result moves after a call and a buffer `write`/`read` are parallel moves, and the allocator tries the register of a value's next use or definition first. Against main 375f849 (`scripts/measure.sh hpLeaf hpCall`): arm64 harness instructions 26,714 → 25,594 (−4.2%), register copies 2,043 → 933 over the 34 harnesses, `mpc` 2,202 → 2,199, `hpLeaf` / `hpCall` executed 395,888 / 441,863 → 370,907 / 416,339 (−6.3% / −5.8%); x64 harness instructions 46,301 → 45,400 (−1.9%), register copies 5,061 → 4,160, `mpc` 3,273 → 3,270, `hpLeaf` / `hpCall` 513,181 / 543,517 → 493,631 / 523,967 (−3.8% / −3.6%). Cost programs (`s:ops6` / extra / `l:ops6`) within one instruction, stack bounds unchanged (arm64 harnesses 7,648, `mpc` 608; x64 7,624, 552); images at `cregs = 0` byte-identical on both targets.

Compile time (`differential time`: `compile` of the suite's 170 programs for both targets, compiled code, a loaded 8-core host; ±20%): allocation off 5.0–6.6 s, on 5.0–6.6 s (no measurable difference); the allocator alone 0.35–0.65 s over the 170 programs (the spike's list-based one: 1.9 s, and it ran three times per compile). The checker is under 0.1 s.

## Proof burden

**Proof burden** (`scripts/proof-burden.sh`):

| | program | contracts | proofs before | proofs after | burden |
|---|---:|---:|---:|---:|---:|
| `Reqs` (Top/Requests.lean, the module) | 23 | 5 | 17 | 2 | 0.96× → 0.30× |
| `pooltally` (Top/Tally.lean) | 32 | 10 | 7 | 7 | 0.53× (unchanged; `Tally.step`'s contract no longer needs the `vcgen` workaround) |
| the reviewer's reactor (Tests/Reactor.lean) | 38 | 11 | 8 | 8 | 0.50× (unchanged) |
| `Bump` module (`#mp_report`) | 70 | 22 | 106 | 84 | 1.83× → 1.51× |
| Lib/ByteBuf.lean | 37 | 16 | 74 | 54 | 2.43× → 1.89× |

## Safety proofs (census)

**Safety proofs over the whole tree** (census of the registry, `Millipede` and `Tests`; "by
hand" is split into `mp_auto` one-liners and other `mp prove`s):

| | `Millipede/` before | after | all before | after |
|---|---:|---:|---:|---:|
| total (`Exp.safe_of_total`) | 22 | 22 | 246 | 246 |
| the analyser alone | 3 | 3 | 36 | 36 |
| the analyser in part, the rest by `mp_safe` | 2 | 2 | 3 | 3 |
| `mp_safe` (automatic) | 10 | 10 | 86 | 86 |
| `mp prove … := by mp_auto` | 3 | 21 | 6 | 24 |
| other `mp prove` (by hand) | 26 | 8 | 51 | 33 |
| open | 0 | 0 | 345 | 349 |

Rerun on 2026-11-19 with `scripts/census.lean` (1.4 s once Millipede and Tests are built): 858
definitions, of which 324 have no obligations, 160 are proved automatically (45 with the
analyser), 8 by hand and 366 have no safety proof. Of these 366, 327 are functions and harness
steps of the differential suite, compiled with `mp.autoSafe false`, and 39 are tests of what the
automation leaves open; none is in `Millipede/`. The differential suite therefore runs the
compiler on programs outside the theorem's premise, which a test of the trusted models allows,
since every run exercises the same models whether or not the program's obligations are proved.

## Core passes (phase 4b)
Static instructions of the 170 differential functions (register allocation on; x64 then with slot locations), passes off / on: x64 1,025,629 / 821,993 = 1.248, arm64 606,650 / 491,927 = 1.233; the 23 literal-argument harnesses 1.480 / 1.447 (compile-time evaluation of calls), the 147 input-driven ones 401,185 / 400,149 = 1.003 and 1.001. Executed (qemu): revchunks −3.0 % on x64, sLoop −1.2 %, rPlainSum −0.4 % (arm64 at most −0.1 %); pooltally, reqs*, readcount, seven other input-driven harnesses and the cost programs unchanged.
