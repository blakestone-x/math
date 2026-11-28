# Source scope and bounded prior-work checks

Recovery check date: **2026-11-28**. This file records the source assertions and the limits of the prior-work search. It does not assert worldwide priority. The sources and proof files were recovered after a workspace reset; the accompanying build logs were regenerated from source and were not reconstructed from earlier lost logs.

## Immutable source statements

The four source snapshots use OEIS data revision `091a90f51479669655f4e46343867ea2abd5d4ff`. Their byte counts and SHA256 digests are in [sources/manifest.json](sources/manifest.json).

| Entry | Selected assertion and attribution | Frozen source |
|---|---|---|
| A202253 | R. H. Hardin's length-three zero-sum bounded arrays; Clark Kimberling's floor formula, April 12, 2012; the recorded empirical recurrence; Colin Barker's generating function, March 3, 2018 | [A202253.seq](https://github.com/oeis/oeisdata/blob/091a90f51479669655f4e46343867ea2abd5d4ff/seq/A202/A202253.seq) |
| A202254 | Hardin's length-four arrays; Barker's parity formulas and generating function, March 3, 2018; the recorded empirical recurrence | [A202254.seq](https://github.com/oeis/oeisdata/blob/091a90f51479669655f4e46343867ea2abd5d4ff/seq/A202/A202254.seq) |
| A202252 | Parent table defining the family and identifying its rows | [A202252.seq](https://github.com/oeis/oeisdata/blob/091a90f51479669655f4e46343867ea2abd5d4ff/seq/A202/A202252.seq) |
| A143978 | Known floor-sequence background associated with the triple formula; its algebraic identities are not a new claim here | [A143978.seq](https://github.com/oeis/oeisdata/blob/091a90f51479669655f4e46343867ea2abd5d4ff/seq/A143/A143978.seq) |

Both selected sequences count ordered arrays, with entries in `[-n,n]`, total sum zero, and each consecutive difference in `[-n,n]`. There is no last-to-first adjacency condition. The formal definitions are cardinalities of the literal finite sets. The proof supplies the bridge from those counts to the recorded formulas.

Both source offsets are one. The natural array count at zero is one, but the source generating functions have zero constant coefficient. The source recurrences follow for `n≥6`; their natural extensions also satisfy the displayed recurrence at `n=5`. The generating-function proofs explicitly account for this distinction.

**Scope excluded:** A202253's separate comment about triples satisfying `w+2x+3y=0` is not a theorem of this package. **Counting policy:** the length-three and length-four results form one mathematical family covering two source entries. Derived recurrences and generating functions are not counted as additional families.

## Existing formal material inspected

### Open Math Agents

The fresh exact-ID search returned one A202253 file and no A202254 file. We read the returned immutable [A202253 statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/250e4c2d5e1ab9e72b355638e380ba2d598a5527/statements/oeis-a202253.lean). It defines the literal filtered finite set and states Kimberling's formula for `n≥1`, but its `main` theorem ends in `sorry`. It credits an AI formalization with Claude Code submitted by `jleguina`. This is an existing statement, not an inspected completed proof. Earlier selection-stage inspections of revisions `4b8cc2ac8b333fd67b340deabf18f953e8cdcbc2` and `ea1e36f03c18db17e965436584565254807e6c7e` had the same relevant admitted statement.

### Sequencelib

We reread [Sequencelib's synthetic A202253 definition](https://github.com/provables/sequencelib/blob/dfb06c18bba196b5aa5bcb3725fe9d201fb9a61a/Sequencelib/Synthetic/A202/A202253.lean). It implements the floor expression as an arithmetic sequence. That file does not identify the expression with the cardinality of the source arrays. Its authorship credits Walter Moreira and Joe Stubbs for the Lean integration, and Thibault Gauthier and Josef Urban for the original synthesis. The arithmetic expression and that implementation are prior work; the selected assertion here is the all-parameter counting identity.

## Completed neighboring result checked semantically

The fresh search for `"zero-sum"` in `kolinhuang0427/open-math-results` returned three files concerning A100691. We read the complete [A100691/A193641 proof](https://github.com/kolinhuang0427/open-math-results/blob/f4fea05c78ea954ace0f1d51da6c9c189e68ccf0/targets/oeis-A100691/PROOF.md). It concerns triangular-strip self-avoiding paths and arrays over `{-1,0,1}` in which every position belongs to a zero-sum contiguous block of length one or two. Those are different counting conditions from fixed-length arrays over `[-n,n]` whose total sum and consecutive differences satisfy the present bounds. It therefore does not settle the selected assertions by renaming them. This comparison uses the definitions in that completed proof, not just the absence of an OEIS identifier.

## Fresh bounded query receipts

[sources/prior_search_receipts.json](sources/prior_search_receipts.json) records the successful recovery-stage GitHub code queries. Each result reported `incomplete_results=false`; that flag describes the returned search result, not exhaustive coverage of all mathematical literature.

| Repository and query | Result |
|---|---|
| `kolinhuang0427/open-math-results`: A202253, A202254 | Zero hits for each exact identifier |
| `kolinhuang0427/open-math-results`: `"zero-sum"` | Three A100691 files; completed proof inspected as above |
| `blakestone-x/math`: A202253, A202254 | Zero hits for each exact identifier before publication of this package |
| `the-omega-institute/trureturing`: A202253, A202254 | Zero hits for each exact identifier |
| `GuillaumeBAUD-coder/open-math-agents`: A202253 | One admitted statement, inspected above |
| `GuillaumeBAUD-coder/open-math-agents`: A202254 | Zero hits |

Four initial recovery queries hit the provider's rate limit. They were subsequently retried successfully; only successful results appear in the receipt file.

## Earlier selection-stage checks and limitations

Before the workspace reset, both available web search engines were used for the exact sequence identifiers, formula authors, bounded zero-sum arrays and adjacent-difference phrases, and distinctive cubic coefficients. Relevant results included the official entries and formal material identified above. A broader Hardinian-array paper concerned king-distance conditions, rather than these exact arrays. Exact-ID searches of `google-deepmind/formal-conjectures` did not return a selected proof. Global Lean and TeX identifier hits outside the cited formal material included unrelated hexadecimal or data occurrences.

The user's repository was also inspected at pre-publication head `47bb2bf83f8b84726f3edae55bade532a9c8350a`, including its README and Lean, Markdown, TeX and sequence text. That inspection found no equivalent selected result. These earlier web and semantic checks are retained as a description of work observed before recovery; the current receipt file does not present them as newly rerun searches.

No completed proof of the two selected counting assertions was found in the material inspected. That is a bounded search conclusion. It does not establish that the assertions have never been proved elsewhere, that every source still labels them open, or that the generic floor and quasipolynomial algebra is new.

## Formal and computational evidence

The seven frozen Lean modules prove the literal triple count, literal quadruple count, parity/floor formulas, recurrences and exact source generating functions. The recovered package's author build is recorded in [verification.txt](verification.txt), with all seven explicit roots, source hashes, compiler and dependency revisions, and standard-axiom output. A separate source-only build and substantive review are performed before publication.

[verify.py](verify.py) and its real [verification-python.txt](verification-python.txt) output check all 49 and 39 frozen source terms, direct triple counts through `n=50`, direct quadruple counts through `n=18`, all 190 nonnegative middle-sum slices in that quadruple range, slice sums through `n=499`, and recurrence/generating-function coefficients through `n=999`. These finite replays support inspection and indexing checks; the unbounded proofs are the Lean theorems.
