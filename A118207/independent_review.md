# Independent review: A118207

Reviewer: sequences12, a separate review agent with no contribution to this package's proof sources. Reviewed November 27, 2026.

## Verdict and scope

**PASS for the exact A118207 conjectural product identity.** I inspected all seven Lean modules, the literal OEIS export, the source and prior-search dossiers, README, and the complete human manuscript section. I also independently read all four pages of Bala's primary note. No mathematical or source-binding defect was found. The theorem proves equality of the two complete formal power series in every degree.

This is an independent review within the collaborative run, not a claim of external journal review or exhaustive historical priority. The arithmetic lemmas, known helper, and product-construction bridge are parts of one resolved source assertion.

## Primary source and attribution

I separately fetched the official immutable OEIS-data export at commit `06e6099a75de062401e2ebfc79a2cefc9686ca69` and compared its bytes with `sources/A118207.seq`; they match. The SHA-256 is `1f100ff7a787d6c39cf54b4229d8d0d6b831d1d16ee0e2dfe1dac7d151c139c1`. The entry defines A(X) as the product of (1+X^n)^λ(n) and records Bala's April 5, 2023 conjecture for A(X²). The formal left factor is precisely (1+X^(2n))^λ(n), and the right factor uses the usual cyclotomic polynomial at X^n and at (−X)^n. Index zero is explicitly neutral, so the products start at the source's index one.

Bala's four-page note, *Cyclotomic polynomials and the generating functions of A118205 and A118206*, dated April 9, 2023, has SHA-256 `7e8d3a95f13878cd22ded32670b051b5d7be2baa70b3809043ffda9f0d8c037d`. Its Proposition 1 proves the helper relating the minus-sign Liouville product to the cyclotomic product. Proposition 2 proves a reciprocal formula. The note does not state the paired X/−X identity in A118207. The package correctly attributes the helper and its Möbius regrouping to Bala, while supplying a full formal proof of the additional identity.

## Mathematical audit

1. **Liouville signs and square divisors.** The definition counts prime factors with multiplicity, with λ(0)=0 only as a neutral extension. Complete multiplicativity is established with nonzero cases justified. The relation λ(2n)=−λ(n) has the correct sign. The square-divisor proof includes uniqueness of the squarefree-times-square decomposition and proves that every other Möbius summand vanishes. It does not assume the desired Euler product.

2. **Cyclotomic normalization.** The normalized first polynomial is 1−X and all later polynomials are the ordinary cyclotomic polynomials. The divisor product is 1−X^n, including its sign at n=1. Multiplicative Möbius inversion is applied in a group of proved units. The literal paired-product bridge removes the two normalizing signs by a proved identity; no sign convention is silently imposed on the source polynomial.

3. **Finite support before regrouping.** All algebraic product arguments are first made at a nilpotent element of an arbitrary commutative ring. The factors 1−x^n for positive n are proved units. A nilpotence bound supplies finite multiplicative support. Index-zero terms are neutral, including the zero coordinates in the rectangular square-factor product. Thus the finite regroupings do not depend on an undefined or nonconvergent infinite product.

4. **Both fiber regroupings.** The square factor indexed by (a,d) is (1−x^(ad²))^μ(a). Grouping first by ad recovers the scaled normalized cyclotomic factor using its divisor antidiagonal. Grouping by ad² recovers the Liouville exponent through the proved square-divisor sum. The finite-support and finite-box lemmas establish that all potentially nontrivial factors are covered. This fully proves Bala's helper inside Lean rather than admitting it as a premise.

5. **The even/odd identity.** At an odd index, pairing the factors at x and −x produces 1−x^(2n); at an even index it produces (1−x^n)². Reindexing with λ(2n)=−λ(n) yields exponent −λ(m) at odd m and −2λ(m) at even m. The quotient factor (1−x^(4n))/(1−x^(2n)) produces exactly the same exponents. Its value is proved to be 1+x^(2n). This gives the desired plus-sign product with the correct square substitution.

6. **Literal source factors.** `plusSeriesUnit` is constructed from the actual power series 1+X^n and proved to have that value. The cyclotomic factors are ordinary mathlib polynomials evaluated at the exact source arguments. The quotient maps preserve those evaluations, unit integer powers, and the paired normalization identity. Consequently the formal source theorem does not rely on a separate assumed source-to-model bridge.

7. **All-degree formal products.** `formalProduct` takes the coefficient in degree n from the prefix through index n. The source tail lemmas prove that every later factor becomes 1 modulo X^(N+1). `cutMap_prefix_stable` and `cutMap_formalProduct` then prove compatibility of these prefixes for every N. The quotient ideal's coefficient-separation lemmas show that equality in every such quotient implies equality of the series. There is no fixed cutoff or unproved analytic convergence condition.

8. **Final endpoint.** `source_conjecture` identifies the literal two formal products in ℚ[[X]], and `source_coefficient_identity` applies to every natural-number degree. `full_resolution` combines these conclusions. The formal theorem is the entire recorded product identity, not merely agreement of a computed prefix.

The human proof agrees with these steps. A minor wording correction was made to the blanket finite-prefix statement: the individual unpaired ordinary-cyclotomic product needs its index-one constant sign even in degree zero. The index-N prefix bound is valid for the two target paired families and the normalized factors; the broader statement uses max{1,N}. This has no effect on any Lean source or theorem.

## Supplementary independent replay

`independent_replay.json` records a separate exact-integer calculation through degree 60. I computed the Liouville signs by trial division, formed the left product and the unscaled defining product directly, and formed the right product from ordinary cyclotomic polynomials with literal substitutions. All coefficients of the two sides agree, the odd coefficients vanish, and the unscaled product agrees with every OEIS-listed coefficient through degree 60. This check specifically corroborates the substitutions, sign at index one, and source coefficient convention; it is not used to justify the all-degree theorem.

## Fresh build and axiom audit

The fresh isolated build in `independent_build.log` rebuilt all seven local proof modules from copied source/configuration files, with no local proof objects reused. It used Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Every local proof module is an explicit Lake root. The build completed with exit code 0.

The printed principal endpoints depend only on `[propext, Classical.choice, Quot.sound]`. Source inspection found no admitted proof, custom axiom, or `native_decide`. After completion I compared every copied Lean/configuration file in the isolated directory with the final package; every byte matched. The independent replay record preserves that comparison and the reviewed hashes.

## Prior-work scope

I reviewed the supplied bounded search record, including exact-ID and semantic searches, both web engines, global GitHub, ProveIt, and trureturing. It distinguishes sequence implementations from a proof, records successful retries after rate limits, and avoids treating an empty indexed search as an exhaustive repository audit. The known primary helper is explicitly credited. The statement that no earlier settlement was located is appropriately limited to inspected evidence; the package does not claim established worldwide priority.

## Reviewed source, configuration, and document hashes

- `Arithmetic.lean`: `84a567b418c8af3d509dc0d407595f41255064443f1a5015f872a0b9563a033e`
- `CyclotomicUnits.lean`: `db7b4d27f042ffd7236877b8657c0e5dc35fa36778eb23c1848b879480b917f5`
- `EulerRegroup.lean`: `cc73f8747a60a6f4cd722dbacd31d1724944b975a2a777715d114a319a1ed911`
- `FiniteProducts.lean`: `2c430cf7196d5dc6b3c3f2e863e5a4fee7375c43df7269296221b5c50ab585da`
- `FormalProduct.lean`: `8dd5be1f7a0c2a7a9b7e521ba1d823403fa32dc76925cd598fa7550dda15f3ee`
- `Proof.lean`: `1e68f5b8ec4c4f808b042433222c2bc3d9f0cf3ecaf2fc702c23c9495078b8e3`
- `SourceSeries.lean`: `00dad070218609aef62bd16be76307db20f2504ce2f48c4818354117eb3b2103`
- `lakefile.lean`: `bd86387e72d658612cadc06d6a9c8d77ef693bcfaa787f654ebfff3dcaa2c781`
- `lean-toolchain`: `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea`
- `lake-manifest.json`: `7fd045d411c0f3f11f63ea289874dc104491292400f5f5456db7610dde660e34`
- `README.md`: `faebc9ad418cb92ad9f7415cc6b22205418145ee2b2ccaaa09a333e3b1330bb4`
- `source_checks.md`: `d14389de8bf5f8ebf3312613e929490df25cfe32b1a7d4388a30eb365465fb2e`
- `manuscript-section.tex`: `1aad20ab163a5c91bc3c5aad0424fd1320a72f258afce801e2935326aadc533d`
- `prior_search/search_summary.json`: `e2bf711e19c01a22f2a36a265172ef6c62c8a0ee6650fab8324168898a615a77`
- `sources/A118207.seq`: `1f100ff7a787d6c39cf54b4229d8d0d6b831d1d16ee0e2dfe1dac7d151c139c1`
