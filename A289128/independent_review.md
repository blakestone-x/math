# Independent review: A289128–A289131

**Verdict: PASS.** Reviewed on 2026-11-27 by an agent independent of the package's proof author. No proof-source changes were requested or made.

The review covers all six Lean modules, the original OEIS definitions and conjectures, the README, the source notes, and the manuscript section. A fresh isolated `lake build` compiled every local module from source and completed with exit code 0, without warnings. The full transcript and source hashes are in [independent_build.log](independent_build.log).

## Primary-source fidelity

All four official exports were independently retrieved from `oeis/oeisdata`. Their returned Git blob hashes match the hashes calculated directly from the package's saved bytes:

| Entry | Revision | Matched Git blob |
|---|---|---|
| A289128 | 7 | `9d7d17a994348a375461510c9f7d98502c8e6137` |
| A289129 | 4 | `9bf9dc96712ee5d5e7ae27d18c24565f70bc69c9` |
| A289130 | 6 | `e0fb2b25700ab3f7cdf10aae04289285aaad9b91` |
| A289131 | 19 | `64fb3d4aefee15f68b0ca5ac63386d220216b59f` |

The primary statements are [A289128](https://oeis.org/A289128), [A289129](https://oeis.org/A289129), [A289130](https://oeis.org/A289130), and [A289131](https://oeis.org/A289131). The saved programs use exactly the three nonoverlapping `StringReplace` rules implemented in `Blocks.lean`.

The formal scanner consumes matched pairs from the input and appends their output without rescanning it in the same pass. When the next two input symbols are `11`, it copies the first symbol and continues from the second; a final singleton is copied. The first six literal words and their lengths agree with the source. There is no unproved replacement of the original scanner by a scalar recurrence.

## Mathematical and formal obligations checked

### Scanner boundaries and exact words

`rewrite_pair` is proved for an arbitrary suffix. This is the needed boundary-sensitive identity: arbitrary concatenation preservation is neither assumed nor used. `core_scanner` simultaneously proves the exact image of the core word and that scanning a core followed by a suffix leaves no pending input symbol. `word_blocks` derives both parity formulas for the actual recursively defined iterates.

The count formulas follow by induction on those explicit blocks. The integer exponent identity `size m + 1 = 2*2^m` handles the natural-number subtraction in the informal formula without any truncation issue. The terminal `10` statement is proved for the core and every positive even iterate.

### Infinite word and stabilization

`word_nested` includes the initial word `00`, and `word_prefix_of_le` extends nesting to all later stages. The definition `bit i = (core i).getD i false` is supported by the bound `i+4 ≤ (core i).length`; its default value cannot affect any requested coordinate. `core_infinite_prefix` explicitly handles both possible orders of the coordinate and core indices.

`word_infinite_prefix`, `bit_stabilizes`, and `infinite_word_unique` prove that this is the actual unique infinite limit of the original iterates. Stabilization is at every stage `n ≥ 2*i+1`, with a simultaneous proof that the coordinate is in bounds. No arbitrary infinite extension is substituted for the source word.

### Occurrence positions and index conventions

The function `position b k` uses `Nat.nth` at rank `k-1` and shifts the resulting zero-based index by 1. The formal specification is required for every positive rank. The value at rank zero is immaterial to the limiting statements at `atTop`.

`count_list` identifies `Nat.count` in a finite prefix with its actual list count. `position_prefix_end` uses `Nat.nth_count` for a known occurrence, so its endpoint equality does not require an assumed density or a conjectural enumeration formula. `positions_of_ends`, `odd_positions`, and `even_positions` then prove the exact endpoint positions in the infinite maps. `infinite_occurrences` establishes that both symbol sets are infinite, and `position_spec` proves every positive rank has the right letter and exact preceding count.

### Exact recurrence domain

The independent `reference` sequence is integer-valued and has all six initial values `2,4,7,11,18,28`. Its recursive branch begins at `n+6` and uses the source coefficients `(1,3,-3,-2,2)`. The proof includes the exceptional index zero. `original_length_conjecture` therefore identifies the original word lengths with the precise source recurrence at every index; it does not exploit natural-number truncated subtraction or an altered recurrence start.

Colin Barker's already-recorded parity formulas are properly credited. The new claim concerns their source-definition bridge, not discovery of those scalar formulas.

### Subsequence limits and nonconvergence

Both `oddRank` and `evenRank` are proved strictly increasing for each symbol. The four ratio limits are therefore along occurrence ranks tending to infinity, rather than along bounded or repeated indices.

The formulas for both numerators and denominators are derived from the original prefix counts and the infinite occurrence-position theorems. The analytical reduction divides by the nonzero factor `2^m`; it uses standard real limits `m/2^m → 0` and `1/2^m → 0`. The four proved limits are:

| Symbol | Odd-stage rank subsequence | Even-stage rank subsequence |
|---|---|---|
| 0 | `5/2` | `7/3` |
| 1 | `5/3` | `7/4` |

`zero_ratio_no_limit` and `one_ratio_no_limit` compose a hypothetical full limit with both unbounded rank subsequences, apply uniqueness of limits in the reals, and contradict the distinct constants. The source-specific refutations and the stronger all-real-limit exclusion thus apply to the actual infinite sequences.

## Build and trust review

The reviewed package pins Lean **4.19.0** and mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**. The independent build used a new directory with copies only of the six local Lean modules, Lake configuration, toolchain, and manifest. No local `.olean` or `.ilean` files existed in the new directory before the build. Only the pinned external mathlib and dependency cache were reused.

The build reports the principal theorem dependencies as subsets of `propext`, `Classical.choice`, and `Quot.sound`. A separate source scan found no `sorry`, `admit`, additional `axiom`, `unsafe`, or `native_decide` declaration or use.

The reviewed proof hashes are:

| Module | SHA-256 |
|---|---|
| Blocks.lean | `6add29086b5a60e96b3e04d58d23642cc075b07488a20326b23276caf4adf086` |
| Counts.lean | `233696500229089963a050bc65bb9ab82e404376f9e79f97b6b2c4ef9d48018a` |
| InfiniteWord.lean | `1c0589fa668737f2530666c05ef364a9a5bc93a2491880e30b9aac459550331a` |
| Lengths.lean | `29652ec770bd21996baa76200804a130c123b7b4c4a936e8e1fb200db075b1f7` |
| Limits.lean | `74567b6ba3152116bde0acf8abf62b611dbdb6cf35524ce0f7b81535662d5f08` |
| Proof.lean | `b63cd835b955754b4f8ab4a8e69ba4f6fc9f19e2785c3132647a6364a55b6637` |

## Scope and bibliographic limits

The package supports exactly one shared length-conjecture proof and two position-limit refutations, strengthened to nonconvergence. The repeated length assertion in A289128 is correctly counted once. The accompanying all-index strict inequalities are not claimed to have a corrected classification. The four displayed subsequential limits are not asserted to exhaust the cluster set or to identify exact liminf and limsup.

The author's bounded prior-publication checks were reviewed. Independent exact-ID and semantic searches were also repeated with both available web engines, including the scanner images and the refuting constants; no earlier resolution of these exact assertions was located. That does not certify historical priority or replace expert bibliographic review. The documented nearby results use different replacement rules.

**Final assessment:** the literal-source bridge, indexing, infinite-word construction, occurrence enumeration, universal recurrence theorem, and real nonconvergence conclusions are complete and correctly represented by the package documentation.
