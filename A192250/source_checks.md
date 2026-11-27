# A192250/A192251 source and prior-work checks

Checked November 27, 2026. This is a bounded search record and an exact interpretation of the selected assertions. It does not certify worldwide priority.

## Exact source

| Entry | Internal revision | Selected content |
|---|---|---|
| [A192250](https://oeis.org/A192250) | 8, December 4, 2016 | Constant component; Mathar's May 4, 2014 recurrence explicitly labelled conjecture |
| [A192251](https://oeis.org/A192251) | 16, September 8, 2022 | Linear component; the identical Mathar recurrence explicitly labelled conjecture |
| [A192232](https://oeis.org/A192232) | 58, September 12, 2026 | Definition of iterative polynomial reduction and the linked 2026 Wiktorowicz note |

The first two immutable OEIS-data snapshots are at commit `571197984aeda7b8b680fe3a1f6a43f9898cd441`, exported November 24, 2024. The defining A192232 snapshot is at `9a78c932ddd46088e3cddc37185bdcd858df3cd1`, exported September 27, 2026. Export dates and the entries' internal revision dates are different metadata. The literal retrieved UTF-8 bodies are saved under `sources/`; `sources/manifest.json` records their exact URLs, byte counts, SHA-256 hashes, and equality to the retrieved bodies.

Both target sequences start at index 1. A192250's program builds `t` with input degree `0..30` and extracts `Part[t,n]` for `n=1..30`. Thus its source index `n` means the polynomial `sum(k=0..n-1, binomial(2k,k) X^k)`. We preserve that convention rather than shift the sequence to offset 0. The claimed recurrence contains `n-3`, so the full valid original-index statement is every `n≥4`.

The source definition in A192232 divides by `X²`, replaces `X²t+r` by `(X+1)t+r`, and repeats. The Lean proof implements this algorithm, proves its degree decreases, and proves equality to remainder modulo `X²-X-1`. The recurrence endpoints use that actual algorithm, not a definition manufactured from the conjectured recurrence.

## Web searches

Both search engines were used for exact identifiers, the named recurrence, and the underlying mathematical construction. Queries included:

- `"A192250" proof recurrence`, `"A192250" "recurrence"`;
- `"A192251" "proof"`, `"A192251" "recurrence" proof`;
- `"central binomial" "reduction" "Mathar"`;
- `"central binomial" Fibonacci partial sums recurrence Mathar`.

Returned material included the exact OEIS source, mirrors, finite sequence-matching suggestions, general binomial/Fibonacci literature, and a distinct proved Mathar recurrence for A113409. No proof of the selected A192250/A192251 recurrence was identified in the returned material. Absence from search results is not treated as an exhaustive literature proof.

## Global GitHub search

`global_search.json` records actual returned URLs, with a limit of 30 results for each query:

- `"A192250"` and `"A192251"`;
- `"5*n-7" "3*n-8"`;
- `"central binomial" "reduction" "Fibonacci"`;
- `"Fibonacci" "binomial" "Mathar" "recurrence"`;
- `"central binomial" "x^2" "x+1"`.

Some exact-ID matches are incidental hexadecimal strings or the unrelated Korean stock ticker. These are excluded by content. The relevant returned program files were inspected in full:

- [jOEIS A192251.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a192/A192251.java) implements the already recorded sum `sum(i=0..n-1, Fibonacci(i)*binomial(2i,i))`. This is a generator for Campbell's known formula, not a proof of Mathar's recurrence.
- [LODA A192250.asm](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/192/A192250.asm) and [A192251.asm](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/192/A192251.asm) are loop-based binomial/Fibonacci generators. They contain neither a proof of the selected recurrence nor its bridge to the polynomial-reduction definition.
- The OEIS ATP benchmark [A192250.smt2](https://github.com/ai4reason/oeis-atp-benchmark/blob/4a80a91728dffea1407ee2f0b8f55622761935cc/pb/A192250.smt2) and [A192251.smt2](https://github.com/ai4reason/oeis-atp-benchmark/blob/4a80a91728dffea1407ee2f0b8f55622761935cc/pb/A192251.smt2) encode **unbounded equivalence of two synthesized integer programs**: their solver query asks whether a nonnegative input exists at which `small` and `fast` differ. They are not merely finite-prefix tests. However, neither inspected SMT problem states Mathar's order-three recurrence or the source polynomial-reduction semantics. Their existence therefore does not supply the selected proof and is expressly disclosed.
- OEIS-Spider copies reproduce the conjectural source statements. OEIS-synthesis/oeis-alien list occurrences do not supply the selected mathematical proof.
- The semantic coefficient query returned `gfis/OEIS-mat`'s `rectopost.man`, `dfinite.grep.txt`, `hologfm.man`, `aphrec4.man`, and `holom.man`. Each was fetched at commit `3a2ac86e6f436bb0c3f373d1b292a50caebad100`; none contains either target ID. These broad recurrence collections are not treated as proof of a negative claim.

## Current formal repositories

Targeted searches of `VladimirReshetnikov/ProveIt` and `the-omega-institute/trureturing` used `A192250`, `A192251`, `central binomial reduction`, and `5*n-7 3*n-8`, each with limit 30. Exact identifiers and the distinctive coefficient query returned no matches. The semantic query returned work on different central-binomial transforms, Gaussian q-binomial identities, factorial parity, and analytic series; its returned excerpts do not contain the selected source recurrence.

Current heads observed separately through the GitHub API were:

- ProveIt: `26d30b08a30e969d1af5ba9e702c4ca5b1daabfd`, November 27, 2026, 21:24:48 UTC.
- trureturing: `66615771c6b1ac838521edbc757411a8e05fc1f5`, November 27, 2026, 21:25:47 UTC.

The search index returned older indexed commits. Head observations do not imply complete indexing of those heads. `prior_search.json` preserves the compact query receipts and observed heads. The local publication catalogue was also checked to exclude an earlier fleet result for either target.

## Closely related primary literature

1. Rafał Wiktorowicz, [*Generating functions for reductions by x²→x+1: proofs of the empirical formulas*](https://oeis.org/A192232/a192232.pdf), 2026. All three pages were read. Lemmas 1–2 establish reduction as a monic remainder and the Fibonacci-weighted sums; these are credited supporting results. Theorem A assumes a polynomial input sequence `b(k)` of degree `d` and gives a rational generating-function denominator dividing `(1-x)(1-x-x²)^(d+1)`. Its explicit table covers A192142–A192146, A192244–A192247, A192254–A192257, A192299, A192304, and A192309–A192312. It also discusses the C-finite Lucas input A192068. It does not state the selected central-binomial-input recurrence or include A192250/A192251 in its table. No new general reduction theorem is claimed here.

2. Richard J. Mathar, [*P-finite recurrences from generating functions with roots of polynomials*](https://arxiv.org/pdf/2109.02112), arXiv:2109.02112, 2021. The paper develops general generating-function methods; its overview and examples were inspected, and text searches found neither target identifier nor “Fibonacci.” General holonomic methods are established background, not a novelty claim of this package. Our direct certificate does not depend on a generating-function derivation.

3. Kunle Adegoke, Robert Frontczak, and Taras Goy, [*Binomial Sum Relations Involving Fibonacci and Lucas Numbers*](https://www.mdpi.com/2673-9909/3/4/46), *AppliedMath* 3 (2023), 851–881. The introductory scope and the nearby central-binomial sections were inspected. They treat other binomial transforms and sums with two central-binomial factors; neither target identifier occurs. The inspected statements do not give the selected order-three recurrence. This is a bounded comparison, not a claim to have excluded every identity derivable from the paper.

## Result counted

Exactly **one source family** is resolved: the two Mathar component recurrences, for every source index `n≥4`. We do not count the classical reduction lemma, Campbell's sum formula, the central-binomial ratio, the two coefficients separately, or the supplementary finite checks as additional solved problems.
