# A052392 source and prior-work check

Checked November 27, 2026. This records a bounded search and exact source interpretation, not a guarantee of worldwide novelty.

## Source snapshots

- [A052392](https://oeis.org/A052392), internal revision 12, April 24, 2025. Robert Israel's November 26, 2018 formulas are explicitly labelled empirical. The offset is 0. The included Maple algorithm sets the exceptional value `T(2,1) = 3`.
- Immutable OEIS-data copy: [A052392.seq](https://github.com/oeis/oeisdata/blob/d82525dfc9110d2641b2ce564c673318a3c3007b/seq/A052/A052392.seq). The repository export commit is May 9, 2025; this is distinct from the source's internal revision date.
- [A054120](https://oeis.org/A054120), internal revision 27, January 26, 2022. Its June 2, 2015 Hendel comment already proves the local triangle recurrence. We credit that result, including the reason for its exceptional initial entry. Mathar's January 26, 2022 comment records an apparent bivariate generating function; this package does not count it as a separate solved problem.
- Immutable OEIS-data copy: [A054120.seq](https://github.com/oeis/oeisdata/blob/72c53dd50967ac7166f7d31bf79be95174ec5bc6/seq/A054/A054120.seq). The export commit is April 26, 2023.
- Both exact source snapshots are included under `sources/`; `sources/manifest.json` records SHA-256 hashes.

## Search coverage

Both available web search engines were used for exact identifiers and semantic descriptions. Queries included `"A052392" proof generating function`, `"A052392" "proof"`, `"A054120" "Delannoy"`, `"McGarvey" "subdiagonal" Delannoy proof`, `"McGarvey" triangle "subdiagonal" generating`, and the distinctive numerator/discriminant pair. The returned relevant material was the OEIS source and mirrors, Sequence Machine, the adjacent triangle entry, and generalized Delannoy literature. No exact proof of the two source formulas was identified in the returned material.

Global GitHub file search used `"A052392"`, the recurrence fragments `"8*n" "28*n" "a(n+4)" "a(n+3)"`, and `"McGarvey" "Delannoy"`, each with a 20-result limit. `global_search.json` records the actual returned URLs. Many exact-ID matches were incidental hexadecimal strings. Semantic results contained unrelated OEIS records, coefficient-generation data, or unrelated name co-occurrences. Limits and indexing mean this search is not exhaustive.

The mathematically relevant exact-ID GitHub results were inspected:

- [jOEIS A052392.java](https://github.com/archmageirvine/joeis/blob/abb609413c9b320e769eaf41c0eef4ee43d1b5e7/src/irvine/oeis/a052/A052392.java) selects `T(2n+1,n)` from the source array. Its parent `A054120.java` implements the local triangle recurrence. This is sequence-generation code, not a proof of the claimed subdiagonal generating function.
- [LODA A052392.asm](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/052/A052392.asm) gives a coefficient generator with a recurrence. The file supplies neither a source-array equivalence proof nor a proof of Israel's generating function. Its existence is disclosed rather than counted as negative evidence.

Targeted searches of `VladimirReshetnikov/ProveIt` and `the-omega-institute/trureturing` for `"A052392"` and the related `"A054120" "generating"` returned no matching files. Current repository heads observed during the check were:

- ProveIt: `49af140e6ff2b0d19fa62ff703ccfc0cc25b3e68` (November 27, 2026, 21:04:18 UTC).
- trureturing: `720eb936a3bfd96a946ec055210f018951c4dfaa` (November 27, 2026, 20:51:50 UTC).

These are head observations, not a claim that a search index exhaustively covers those commits. `prior_search.json` preserves the compact query receipts. The existing local publication catalogue was also checked to exclude a previous fleet result for this family.

## Closely related literature

Paul Barry, [*On Integer-Sequence-Based Constructions of Generalized Pascal Triangles*](https://www.maths.tcd.ie/EMIS/journals/JIS/VOL9/Barry/barry91.pdf), *Journal of Integer Sequences* 9 (2006), Article 06.2.4. The retrieved paper's generalized Delannoy discussion and central/subdiagonal examples were inspected; text searches for A052392 and A054120 had no matches. The classical weighted-Delannoy framework is credited. No claim is made that this package originates that framework. The explicit abnormal-entry source triangle and its exact empirical formulas were not found stated as a proved result in the material inspected.

## Scope of the result

The package proves exactly one source family: A052392's empirical generating function and recurrence, for all indices from 0. The recurrence of A054120 and the general Delannoy machinery are supporting prior results, not additional problem counts. The Lean proof starts from the literal algorithm attached to A052392 and establishes all subsequent relations internally. The historical equivalence of that algorithm with A054120's strip-sum presentation is credited to Hendel; it is not silently presented as a new theorem of this package.
