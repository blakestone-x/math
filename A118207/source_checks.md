# Source and bounded prior-work review: A118207

Checks performed November 27, 2026. This file records the exact assertion and the scope of the inspected evidence; it is not a guarantee of worldwide priority.

## Exact primary source

- Entry: <https://oeis.org/A118207>, by Stuart Clary, April 15, 2006.
- Source revision: 29, September 2, 2023 at 20:31:35.
- The target is Peter Bala's FORMULA conjecture dated April 5, 2023: the substitution X ↦ X² in the defining Liouville-weighted product equals the paired cyclotomic product at X and −X.
- Last-touch OEIS-data export commit: `06e6099a75de062401e2ebfc79a2cefc9686ca69`, September 17, 2023.
- Immutable source: <https://github.com/oeis/oeisdata/blob/06e6099a75de062401e2ebfc79a2cefc9686ca69/seq/A118/A118207.seq>.
- The preserved export is [sources/A118207.seq](sources/A118207.seq), SHA-256 `1f100ff7a787d6c39cf54b4229d8d0d6b831d1d16ee0e2dfe1dac7d151c139c1`.
- Liouville background and the source's cross-reference: <https://oeis.org/A008836>.

The exact factor families are formalized in `SourceSeries.lean`. The left side is the defining product with each X^n replaced by X^(2n). The right side uses the usual cyclotomic polynomial Φ_n twice, evaluated at X^n and (−X)^n. Each family has neutral factor at index zero. The individual sign normalization at n = 1 is removed in a proved pair identity; it does not change the target.

## Closest primary proof, credited explicitly

Peter Bala, *Cyclotomic polynomials and the generating functions of A118205 and A118206*, April 9, 2023:
<https://oeis.org/A118205/a118205.pdf>.

The complete four-page PDF was retrieved and read. Its byte length is 137,907 and SHA-256 is `7e8d3a95f13878cd22ded32670b051b5d7be2baa70b3809043ffda9f0d8c037d`. Its content is retained in the research record, not republished here.

Proposition 1, on pages 1–2, proves that the Liouville product of (1−X^n) is the negative of the cyclotomic product Φ_n(X^n). Its argument uses Möbius inversion and the square-divisor identity for λ. Proposition 2, on page 3, gives the reciprocal product involving Φ_(2n)(X^n). The note does not state or prove the A118207 functional identity at X and −X. Two contributors independently inspected the complete note and confirmed this distinction.

The helper and its regrouping are therefore attributed to Bala, not presented as a new result. The formalization re-proves the helper so that the final assertion has no unproved mathematical premise. The named conjecture follows by an additional even/odd product identity.

## Bounded search record

- **Own repository.** Searches of the existing published Lean, Markdown, and TeX files for `A118207` and for Liouville/cyclotomic combinations found no prior package covering this identity.
- **Exact global GitHub search.** `A118207`, with up to 100 returned hits, located the joeis implementation, a LODA program, joeis-lite implementation records, and unrelated occurrences in hexadecimal data or numerical labels. The mathematically relevant hits compute the defining sequence; none of the inspected hits proves the cyclotomic functional identity. The leading joeis hit is pinned at `abb609413c9b320e769eaf41c0eef4ee43d1b5e7`, path `src/irvine/oeis/a118/A118207.java`; the LODA hit is pinned at `f1b383b2344ab03ae8f79f41289360a6bd4394bd`, path `oeis/118/A118207.asm`.
- **Exact scoped GitHub searches.** `A118207` in `VladimirReshetnikov/ProveIt` and in `the-omega-institute/trureturing` returned no hits. A rate-limited trureturing request was retried successfully. The failed request itself is not negative evidence.
- **Semantic scoped GitHub searches.** `Liouville cyclotomic` in ProveIt returned unrelated Fabius-function/q-series and other material, with no settlement of this identity. The corresponding trureturing search was retried after rate limiting and returned no results. Visible repository snapshots in the surrounding checks were `a4404ca0247c31b8760589015b7eb6ab4efb6f92` for ProveIt and `7c3c605dff254e6281ff23265a7faf4b20e7534e` for trureturing; an empty search does not itself identify or certify every file at those commits.
- **Semantic global GitHub searches.** Liouville/cyclotomic product combinations returned generic cyclotomic code, theorem-name lists, and unrelated mathematical works. The returned primary titles were screened for a relation to the identity; none gave a settlement.
- **Both web engines.** Exact-ID and semantic searches for Liouville-weighted cyclotomic products, the paired X/−X functional identity, and the Bala conjecture returned the OEIS entry and the primary Bala helper note. Additional exact-ID searches with Palomar and Hexagon found no relevant publication. No proof of the target was located in the inspected results.

The compact machine-readable record in [prior_search/search_summary.json](prior_search/search_summary.json) preserves query scope and relevant immutable result URLs. Raw search responses, including rate-limit errors and their successful retries, are retained in the research record. Full retrieved articles and complete response bodies are not republished in this package.

Search tools can omit unindexed, differently phrased, or recent work. The claimed contribution is a complete proof and formalization of this exact recorded conjectural identity, not a new general theory of cyclotomic products or a certified historical-priority result.

## Formal scope and verification

The nilpotent theorem is proved in an arbitrary commutative ring. For the source statement, the proof uses all quotients ℚ[[X]]/(X^(N+1)), with no fixed bound on N. `formalProduct` is constructed from finite coefficients, and the tail and stabilization lemmas prove that it has the intended infinite-product meaning. `source_conjecture` therefore proves equality of the literal two formal series; `source_coefficient_identity` applies to every degree.

There is no analytic convergence hypothesis. The formal source identity is stated over ℚ, which contains the integer coefficients of the defining products. This package is counted as one conjectural-formula resolution. The known Bala helper, arithmetic lemmas, and source bridge are parts of that proof, not additional counted problems.
