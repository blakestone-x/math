# A326925: targeted even-degree and constant-term prior checks

Checked November 27, 2026 by the sequence scout independently of the algebra author. This is a bounded check of the **even-degree factorization clause** and the companion Fibonacci/Lucas constant-term observation. The already-published odd-degree result in this repository is prior project work and must not be counted again.

## Exact primary records

All three complete current exports were retrieved through the official `oeis/oeisdata` GitHub connector and read. They still contain the conjectural wording and no new proof link for this target.

| Entry | Official revision | Git blob SHA-1 |
|---|---|---|
| [A326925](https://oeis.org/A326925) | 13; October 31, 2019, 21:41:49 | `e8036d79dbacfa38c832486936d3d80b5472cde1` |
| [A328610](https://oeis.org/A328610) | 12; October 31, 2019, 21:42:22 | `91e469434417481063f3629100c931cc3d2fdce0` |
| [A328611](https://oeis.org/A328611) | 11; October 31, 2019, 21:42:33 | `273ca073f7b24d3ff7ccb59d92f72e14ba0ce7ea` |

The corresponding official GitHub paths are `seq/A326/A326925.seq`, `seq/A328/A328610.seq`, and `seq/A328/A328611.seq`. The previous A326925 package already preserves these identical blobs.

### Degree, derivative order, and scalar normalization

Use degree-indexed polynomials $P_N$, beginning with $P_1=1-x$. The exact rational derivative identity in the existing formal bridge is

$$
\left(\frac{1-x}{1-x-x^2}\right)^{(n)}
=\frac{n!P_{n+1}(x)}{(1-x-x^2)^{n+1}}.
$$

Consequently, the new degree-$2k$ case corresponds to derivative order $2k-1$. The source title and companion comments conflate these indices, but their displayed polynomials and loops over odd derivative orders identify the intended family. Irreducibility is unchanged by nonzero rational scalar normalization. This indexing reconciliation is not a new conjecture resolution.

### Factor order is not a canonical definition

For degree two, A326925 displays $x(2-x)$, whereas the first rows of A328610 and A328611 give respectively $x-2$ and $-x$. Their product is the same polynomial, but the factors are exchanged and both signs changed relative to the natural Fibonacci/Lucas labeling. From degree four onward, the displayed first factor is monic and the displayed second factor has leading coefficient $-1$.

For half-degree $k\ge2$, the displayed constant rows are

$$
1,1,2,3,5,\ldots=F_{k-1},\qquad
1,3,4,7,11,\ldots=L_{k-1}.
$$

A natural normalization extending to $k=1$ gives constants $F_0=0$ and $L_0=2$, with factors $x$ and $2-x$. The main A326925 observation is insensitive to factor order; a claim of literal equality with both companion arrays requires an explicit exceptional first row and a factor-order convention. Mathematica `FactorList` output order by itself should not be used as a mathematical definition of the two families.

The row-sum and alternating-row-sum observations in the companion records are separate statements. They are outside this check's proposed resolution count and require their own index-sensitive bridge if included later. In particular, the printed row of degree two in A328610 has alternating sum $2$, so its short informal index wording must not be copied into an unqualified all-row theorem.

## Search engines

Both available engines were used. Exact queries included:

- `"A326925" (proof OR irreducible OR factor)`
- `"A326925" "even" "irreducible"`
- `"A326925" "proof" github`
- `"A328610" "A328611" (proof OR Fibonacci OR Lucas)`
- `"A328610" (proof OR conjecture)`
- `"A328611" (proof OR conjecture)`
- Each of the three literal IDs with `site:trureturing.org`.

Semantic queries included:

- `"derivatives" "(1-x)/(1-x-x^2)" irreducible`
- `"1-x-x^2" "irreducible" "derivative"`
- `"Kimberling" "even degree" "irreducible"`
- `"Fibonacci" "Lucas" "derivative numerator" factors`
- `"Fibonacci" "Lucas" "rational function" "irreducibility"`
- `"Fibonacci" "Lucas" "constant terms" "factors" Kimberling`
- `"1 - x" "1 - x - x^2" Kimberling polynomial`
- `"1 + 3*x + x^3" "3 + 3*x + 6*x^2 - x^3"`.

Relevant exact-ID hits returned the OEIS records and mirrors. Semantic results returned other polynomial families, generic algebra material, and unrelated catalogue identifiers. No earlier proof of the exact even-degree clause or exact factor constant-term identification was located.

## Primary resolved-results catalogue

The live [trureturing conjectures catalogue](https://www.trureturing.org/conjectures) was opened. Its retrieved page displayed 2,235 resolved results. Searches of the retrieved text for A326925, A328610, and A328611 returned no matches. Searches for Fibonacci, Lucas, Kimberling, and derivative were also inspected; the listed topics were different questions.

Semantic search did locate [Bala's even-step Fibonacci-polynomial integrality conjecture](https://www.trureturing.org/research/bala-a349272/). The primary report was read: its polynomials satisfy $F_0=0,F_1=1,F_{j+2}=XF_{j+1}+F_j$ and its assertion is integrality of a product divided by a sum at even index steps. This is a different polynomial family and different conclusion.

The primary report [Mane's negative-index factorization](https://www.trureturing.org/research/mane-2026-negative-index-fibonacci-factorization/) was also inspected. It concerns a specified negative-index window for $k$-generalized Fibonacci polynomials and a factorization involving $x^k+1$ and $x^k+s$. It does not identify the derivative numerator or the two factors at issue here.

Catalogue absence alone is not evidence of exhaustive historical novelty; the literal and semantic searches and primary-definition comparisons are separate parts of the bounded check.

## Nearby primary literature

1. Dan Levy, *The irreducible factorization of Fibonacci polynomials over Q*, Fibonacci Quarterly **39** (2001), 309–319. The [primary journal PDF](https://www.fq.math.ca/Scanned/39-4/levy.pdf) was opened and its introductory definitions and main-result description read. It treats the standard Fibonacci, Lucas, and Chebyshev-type families with recurrence $y_{n+1}=xy_n+b y_{n-1}$ for constant $b=\pm1$. Those are not the degree-indexed derivative polynomials here. Its cyclotomic-style factorization does not supply the exact two-factor assertion merely because Fibonacci and Lucas names occur in both settings.

2. A. Borisov, M. Filaseta, T. Y. Lam, and O. Trifonov, *Classes of polynomials having only one non-cyclotomic irreducible factor*. The [primary author PDF](https://people.math.sc.edu/filaseta/papers/noncycl.pdf) was opened and its introductory conjectures and theorem statements read. It discusses derivatives of $1+x+\cdots+x^n$ and the Gutkin/Lagarias family $(n-1)(x^{n+1}-1)-(n+1)(x^n-x)$. These differ from iterating derivatives of $(1-x)/(1-x-x^2)$.

The use of a quadratic field, norms, binomial irreducibility, and conjugation descent is standard algebra. Neither the new sufficient binomial helper nor the descent lemma should be counted as a separately resolved conjecture or advertised as a new general criterion.

## Supported conclusion and limitations

The official source still records the even-degree statement as conjectural, and no prior exact proof was found in the checked sources. A complete formal all-index proof may therefore be presented as a proposed resolution of that recorded clause, with bounded historical-priority language. Count the even-degree assertion once across the three entries. If the factor constants are formally proved, describe their exact normalization and indices; do not count the two companion IDs as two additional independent factorization conjectures.

The odd-degree clause was already established in this project. These searches do not establish priority over unindexed, unpublished, or inaccessible work, OEIS editorial acceptance, or a proof of every other observation in the linked entries.
