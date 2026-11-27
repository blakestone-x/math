# Source, domain, and prior-work review

Reviewed November 27, 2026 (America/Chicago). This is a bounded review of the retrieved sources. It does not establish first-publication priority and does not exclude a specialization of older congruence theorems whose full texts were unavailable.

## Exact primary-source snapshots

The four exports below were retrieved through the GitHub connector from the public [oeis/oeisdata](https://github.com/oeis/oeisdata) repository. The saved UTF-8 bytes were checked against Git's blob hash, computed as SHA-1 of `blob <byte-count>\0<contents>`. The hashes match the connector's reported values.

| Saved file | Entry revision and timestamp | Exact Git blob SHA-1 | Bytes |
|---|---|---|---:|
| `sources/A000033.seq` | 60, June 21, 2026, 09:42:14 | `dd7b47b9c48399a10e808ebacc9cdeb9dcbcbfc1` | 2768 |
| `sources/A000159.seq` | 54, June 21, 2026, 09:42:19 | `08dab7ac2feb8f60467e08c74fcdc11e4b83d3e1` | 2103 |
| `sources/A000181.seq` | 30, June 21, 2026, 09:42:33 | `9059953cca1624299eb341610a259cf019d8e3da` | 1438 |
| `sources/A058087.seq` | 66, November 5, 2025, 15:35:29 | `394c485c5f0669e021381ef00569986efae90a90` | 4744 |

Live entry URLs: [A000033](https://oeis.org/A000033), [A000159](https://oeis.org/A000159), [A000181](https://oeis.org/A000181), [A058087](https://oeis.org/A058087). OEIS contributors retain their stated authorship and attribution. All three target statements are attributed in the exports to Mark van Hoeij, June 10, 2019, and remain labelled conjectures in these snapshots.

## Statement fidelity

The common expression is $a(n)+2a(n+p)+a(n+2p)$. The coefficient of the middle term is positive two, and the shifts are by $p$ and $2p$.

| Item | Source convention | Formal counterpart |
|---|---|---|
| A000033 domain | Offset begins at 1; explicit formula is coefficient of $t^2$ | `A000033_prime_shift`, assumption `1 ≤ n`, degree 2 |
| A000033 primes | Every prime | Assumption `p.Prime`, no exception |
| A000159 domain | Offset begins at 3 | `A000159_prime_shift`, assumption `3 ≤ n`, degree 3 |
| A000159 primes | Every prime except 3 | Assumptions `p.Prime` and `p ≠ 3` |
| A000181 domain | Offset begins at 4 | `A000181_prime_shift`, assumption `4 ≤ n`, degree 4 |
| A000181 primes | Every prime greater than 3 | Assumptions `p.Prime` and `3 < p` |
| A058087 row order | Descending polynomial degree | The coefficient of degree $d$ is the triangle's entry $T(n,n-d)$, for $d≤n$ |
| Source polynomial | Rational finite sum over $0≤k≤n$ | `sourceMenage`, literally with that range and summand |
| Zero row | A058087 Maple explicitly returns 1 | `sourceMenage 0 = 1`; same branch in `menage` |
| Integral model | Reindexing with $j=n-k$ | `menage_eq_sourceMenage`, proved for every $n$ |
| Coefficient model | Rational source coefficient is an integer | `hit_eq_sourceMenage`, proved by applying coefficient extraction to the source bridge |
| Prime 2 | Included for degrees 2 and 3 | `two_shift_of_lt_four` proves degrees 0–3 for every positive index |
| Short initial sums | Indices $n<p$ are allowed | `rook_eq_zero`, `menageMod_truncate`, `scaled_menageMod` justify common finite ranges |

A000033's abbreviated triangle description does not itself cover $n=1,d=2$; its explicit coefficient formula does, with value zero. The formal statement includes this source term. The uniform polynomial theorem requires $n≥1$; it is not silently extended to the special zero row.

The source-definition bridge is a proved equality over rational polynomials. It does not assume one of the target congruences or one of the source recurrence conjectures. The final conclusions are divisibility in the integers. There is no hypothesis that a finite check has succeeded and no upper bound on $n$ or $p$.

## Repository and current public-resolution checks

The current project README was retrieved from `blakestone-x/math` main at the beginning of Batch8, with parent-reported head `a2a6825a315f3c1b2d54dacf81960eb6ce4faa50`. A local text search found none of A000033, A000159, A000181, or the ménage family. This is a check of that retrieved snapshot, not a claim about future concurrent additions.

Both available web search engines were used. Queries included exact A-numbers together with `proof`, `conjecture`, `congruence`, `divisibility`, `prime-shift`, and `trureturing`, as well as `menage van Hoeij congruence`. Their useful retrieved results were the OEIS source entries, the classical references below, and the separate trureturing A000159 recurrence result. Many other exact-ID hits were unrelated product identifiers and were excluded.

The [trureturing conjecture index](https://www.trureturing.org/conjectures) was inspected and searched for all three IDs. The retrieved index text had no matching entry, but the separate A000159 research page was found by exact web search. This demonstrates why absence from that index alone was not treated as proof of absence.

GitHub issue searches in `the-omega-institute/trureturing` returned no issue for A000033 or A000181. The A000159 search returned [issue 24301](https://github.com/the-omega-institute/trureturing/issues/24301), concerning Mathar's six-step recurrence. Its full body was read. The corresponding primary project report, [Mathar's six-step recurrence for three-hit ménage numbers](https://www.trureturing.org/research/mathar-a000159-recurrence/), states a theorem for that recurrence and explicitly excludes the separate prime-shift divisibility assertion. That earlier recurrence proof is credited; it is neither claimed nor reproduced here.

Ahaan Kallat's [*Universal Shift Congruences for Weighted Permutation Sequences*, arXiv:2610.15849](https://arxiv.org/abs/2610.15849), was also retrieved as a full PDF because its abstract mentions van Hoeij conjectures. Its extracted full text contains none of the three target IDs, A058087, or the terms `menage`/`ménage`. Its explicitly named van Hoeij application is A000459, in a different generating-function class. This text search and inspected application do not claim to rule out every possible consequence of its general results.

## Classical congruence literature and the unresolved historical scope

The existence and relevance of the following older publications were confirmed bibliographically:

1. L. Carlitz, *Congruences for the ménage polynomials*, Duke Mathematical Journal **19** (1952), 549–552, [DOI 10.1215/S0012-7094-52-01957-1](https://doi.org/10.1215/S0012-7094-52-01957-1).
2. L. Carlitz, *Congruence properties of the ménage polynomials*, Scripta Mathematica **20** (1954), 51–57. These exact bibliographic details also appear in Wyman–Moser's reference list below.
3. Harlan Stevens, *Arithmetic properties of the ménage polynomials*, Rocky Mountain Journal of Mathematics **11** (1981), 635–639, [DOI 10.1216/RMJ-1981-11-4-635](https://doi.org/10.1216/RMJ-1981-11-4-635), [JSTOR 44236630](https://www.jstor.org/stable/44236630). The JSTOR issue contents give pages 635–639; some DOI metadata instead gives 635–640 and misspells the title as “mean age.”

Publisher DOI pages, their advertised download URLs, JSTOR, and zbMATH endpoints were tried. The Euclid endpoints supplied a bot-challenge HTML page rather than the paper; JSTOR supplied metadata without article text; the requested zbMATH text was inaccessible. No login, paywall, or other access restriction was bypassed. **The complete mathematical statements in these three older papers were not verified.** Their relevance prevents a confident claim that the general congruence proved here is historically new, or that the three named OEIS consequences were not already implicit in them.

The full primary PDF of M. Wyman and L. Moser, [*On the problème des ménages*, Canadian Journal of Mathematics **10** (1958), 468–480](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/48A61575419059312835F7B241D2DE8D/S0008414X00045715a.pdf/on_the_probleme_des_menages.pdf), DOI [10.4153/CJM-1958-045-6](https://doi.org/10.4153/CJM-1958-045-6), was read. It contains generating functions, Bessel and asymptotic formulas, exact expressions, and tables of ordinary ménage numbers. It credits Riordan congruences for checking the tables and lists Carlitz's papers, but it does not reproduce the polynomial second-shift theorem used here. Reading this paper does not replace reading the inaccessible earlier congruence papers.

The classical defining formula is already attributed in A058087 to Kaplansky and Riordan; the integral rewriting and finite-field argument in this package are elementary consequences of that formula. The package's certified contribution is the complete, explicitly linked Lean proof of the three source assertions and the stated uniform theorem. **No claim of an unprecedented mathematical theorem or of first historical resolution is made.**

## Verification scope

`Proof.lean` was copied with its pinned configuration into a fresh isolated directory and built with `lake build`, reusing only dependency caches. The build passed; [verification.txt](verification.txt) records the output and SHA-256 hashes. The printed axioms of the source bridge, uniform theorem, and all three source assertions are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The code proves statements about the classical source-defined polynomials, including their integral coefficients. It does not separately formalize their combinatorial interpretation as seating arrangements. The reviewed target is the coefficient sequence explicitly used by the source entries, for which the kernel-checked source bridge is complete.
