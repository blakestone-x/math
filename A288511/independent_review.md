# Independent review of A288511

Reviewer: `/root/number12`  
Date: November 27, 2026  
Status: complete — accepted for the exact stated formal theorem.

## Independence and scope

I did not author or modify this package's Lean sources, its state model, or its
conventional proof. I reviewed the literal scanner, the block and boundary
identities, the unbounded word and length bridges, the recurrence certificate,
and the final equality with the independently defined OEIS recurrence. This is
an internal independent review by a separate collaborating agent, not an
external peer review or a claim to certify worldwide novelty.

## Source binding

The archived A288511 entry, revision 9 dated April 7, 2020, defines its sequence
by the displayed thirteen-term recurrence from index 16 and the sixteen
initial values at indices 0 through 15. Its conjecture identifies that sequence
with the literal iterate lengths for `00 -> 0101, 10 -> 001`, starting at `00`.
A288508 supplies the `StringReplace` implementation and the first nine words;
A288512 repeats the same length conjecture.

`Kimberling288511.rewrite` implements the one-pass, left-to-right, nonoverlapping scan:
matching pairs consume two input letters, unmatched letters consume one, and
emitted replacements are not rescanned during that pass. The empty and
singleton cases preserve their source meaning. `word 0 = [false,false]` and
`word (n+1) = rewrite (word n)` retain the source's index zero. I checked the
source words against this interpretation. The three OEIS references represent
one length assertion and are correctly counted once.

The displayed OEIS generating function contains an extra leading `x` relative
to its stated offset zero. The package explicitly documents this discrepancy.
The final Lean claim addresses the independently recurrence-defined sequence,
so it does not silently treat that shifted display as a correct offset-zero
identity. The corrected unshifted rational generating function in the README
is presented as an algebraic corollary, not a separate formal power-series
theorem.

## Mathematical and formal review

1. The block coding `A = 10`, `B = 100`, `C = 1000` and substitution
   `A -> B`, `B -> C`, `C -> AAB` are connected to the literal scanner by
   `rewrite_block`, `rewrite_encode`, and the exact conjugacy `rotation`.
   No unjustified claim that the scanner preserves arbitrary concatenations
   is used.
2. `rewrite_suffix` checks all ten boundary phases with an arbitrary natural
   trailing coordinate. `rewrite_shape` then proves the full transition for
   every token word and every trailing coordinate. The finite phase table is
   a universal local identity, not an extrapolation from ten observed iterates.
3. `word_shape` proves equality of finite binary words at every index from
   nine onward. Its base is the exact ninth literal iterate, and its step is
   `rewrite_shape`. `packed_future` and `literal_numeric_bridge` transfer this
   identity to the affine count state and its length observation. The finite
   count model is therefore tied to the source at every index where it is used.
4. `recurrence_certificate` quantifies over every phase and four unrestricted
   integer coordinates. Its ten case proofs establish explicit intermediate
   affine states and the recurrence identity algebraically. This is stronger
   than checking only finitely many states reachable from the seed.
5. `tail_recurrence` applies from newest index 22. The six remaining instances
   at newest indices 16 through 21 are checked using already proved literal
   values. Thus `literal_recurrence` begins at precisely the source's required
   cutoff. No earlier recurrence is assumed.
6. `source` separately specifies the sixteen source initial values and the
   source recurrence. `all_lengths` uses initial agreement and strong induction
   to prove the literal length equals this reference sequence for every
   natural index, including zero. The target is not weakened to a finite
   prefix, an asymptotic statement, or a recurrence-defined stand-in for the
   source scanner.

I independently replayed the literal rewrite with a separate regular-expression
scanner: all nine words printed in A288508 and all lengths at indices 0 through
21 matched the archived sources. This covers the initial values and the six
finite recurrence instances preceding the universal tail argument.

I also independently recomputed the README's explanatory `R` and `S` expressions
symbolically from its phase table. Their phase constants, the common difference
`S_(n+1) - S_n = -7`, and the degree-thirteen denominator all agree. I also
checked the displayed corrected numerator against the initial data and the
resulting recurrence. These supplementary computations support the written
explanation; the Lean endpoint supplies the unbounded proof.

## Frozen artifacts and verification

The independent command was:

```text
python research/batch10/build_package.py output/batch12/A288511 independent
```

It built every local proof module from source in a fresh isolated directory,
without copying any local `.olean` file. The external pinned dependency caches
were reused. The toolchain was Lean 4.19.0 with mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. All four explicit Lake roots
(`Blocks`, `Counts`, `Recurrence`, and `Proof`) built successfully, and the
process exited zero. The complete transcript is `independent_build.log`.
I checked that its recorded proof/configuration hashes still equal the files
reviewed below.

The explicit axiom report for `all_lengths`, `literal_recurrence`,
`recurrence_certificate`, `literal_numeric_bridge`, `word_shape`, and
`rewrite_shape` contains only `propext`, `Classical.choice`, and `Quot.sound`.
`rotation` uses only `propext`. All ten private phase certificates also report
only the standard three axioms. No `sorryAx` or native computation trust axiom
appears. Source inspection found no `sorry`, `admit`, `native_decide`, custom
axiom declaration, or unsafe declaration.

The exact public endpoint is:

```lean
Kimberling288511.all_lengths (n : ℕ) :
  ((Kimberling288511.word n).length : ℤ) = Kimberling288511.source n
```

The following SHA-256 hashes identify the inspected frozen proof/configuration
files and the source/documentation snapshots used in this review:

| File | SHA-256 |
|---|---|
| `Blocks.lean` | `82cef17807ff684bdfdae2868ae40b42d803df949c5bf01298dfdb7dc9085024` |
| `Counts.lean` | `6488b5fcd77132f831f87e471f040149e6dda3f7a7f782a74995e4f4c4614297` |
| `Recurrence.lean` | `8154b23f0f88c38cb9fe8068ec276673b079f3a94b6db6fb3f88561640fb4178` |
| `Proof.lean` | `9a2918f542a960ef685e093edced30b84342ad8fad13d98d25bfbd6eb026005f` |
| `lakefile.lean` | `c2e1e1b9688e3b2c79128ef5f9d2e27cf361d66f57343b89dad9cd636e99773f` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lake-manifest.json` | `54128eb3c73cb23f8bde76f0298e7d713432d92d38d5b0d7fe2d3ac7a0d144a8` |
| `README.md` | `56f948fc3fda0bd36cd48ac54f449ebc323a01950278b0f6f59b286b20063f25` |
| `manuscript_section.tex` | `6fa96a04943f2db620ce892a01cfd89aa8fd119978a27e74acb386c15d73c054` |
| `source_checks.md` | `a88d7d6c73f721cc2c96aea93d2acf4b4c363bf0fdb869f5fab5ecd93d7157f7` |
| `source_provenance.json` | `dc8a676d236c01c0d0baa13611c5f33a8bdaf28a50000749db9a8b0627945587` |
| `sources/A288508.seq` | `4bdb7073f03dcb4d7282be78900d200317f9841138117c94c5244711e414eb99` |
| `sources/A288511.seq` | `29225f6c27cd4fddd32a58be00e3539c964ecd352d4b299b3a3f16fb14654710` |
| `sources/A288512.seq` | `3b9e79a04bff3453d01b215c1b0d2035586d78e539e34c99c7825332d4a85273` |

## Supplementary provenance screen

I independently searched the current default-branch GitHub indexes of
`the-omega-institute/trureturing` and `VladimirReshetnikov/ProveIt` for the exact
identifier `A288511` and the conjunction of the literal rule strings
`"00->0101" "10->001"`. All four queries returned zero results. During that
supplementary check, the latest visible commit-list results were respectively
`38910d2c96de5f4ed439d8fdc0d31b7f34f0e066` and
`a68af0f507b9a558a8c7e8390e338bd15cc928e2`. The raw tool receipts are archived
in `independent_github_receipts.json`. This is supplementary bounded search
evidence, not an assertion that a search index completely covers a repository
commit or that no prior proof exists anywhere. The author's source checks
record their separate current-head observations and broader semantic screen.


## Findings and conclusion

No mathematical or source-binding defect was found. The one source discrepancy
that matters here—the extra leading `x` in the displayed OEIS generating
function—is correctly documented and does not enter the formal statement. The
finite phase certificate, exact word bridge, cutoff checks, and strong
induction establish the complete asserted length identity.

I accept this frozen package as a complete Lean proof of the stated A288511
length conjecture under the standard Lean/mathlib axioms. This acceptance does
not cover neighboring limiting-word or position assertions, does not count the
repeated conjecture in three entries as three results, and does not certify
historical priority or an OEIS editorial decision.

Signed: `/root/number12`, independent reviewing agent, November 27, 2026.

