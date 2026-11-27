# A327315: source alignment and bounded prior-art review

Checked on November 27, 2026. This is a record of the sources and searches inspected, not a certification of historical priority. The public conjecture text remains present in the checked official OEIS export. An exact polynomial-family connection to earlier literature must be credited even though the inspected irreducibility theorem does not settle this parameter.

## Exact source and statement

The primary record is [OEIS A327315](https://oeis.org/A327315), attributed to Clark Kimberling on November 1, 2019. The saved official export is [A327315.seq](sources/A327315.seq), from the [immutable official export](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A327/A327315.seq). The current raw export and that immutable file were compared byte for byte.

| Record | OEIS header | Export commit | Git blob | SHA256 | Bytes |
| --- | --- | --- | --- | --- | ---: |
| A327315 | revision 6, November 6, 2019 | `571197984aeda7b8b680fe3a1f6a43f9898cd441` | `47efe5bcf666241a43536ea4f106e7342c741f96` | `4cf24334a3be2295bb091e05b507ac500c163688bfacb3bfd8372103fc79c463` | 1753 |
| A069353 | revision 20, April 22, 2025 | `e80c38cadbb935f549ca291ffa8fda702a3ff278` | `aeb2a0ed4dcbaff009e9044abd2c52659409c9bf` | `6926741f40247aef89e3d5f02ba30681f28738dcc0555ba516e418a167f105ef` | 1770 |

Full latest-file-commit metadata is preserved alongside each export. The export commit dates are November 24, 2024, and May 7, 2025, respectively; these are export-history dates, not conjecture dates.

A327315 defines its row polynomial by taking the reduced numerator of the nth derivative of

\[
f(x)=\frac{x-2}{x^2-x+1},
\]

and dividing by n!. Its Mathematica program starts at n=0, as do its rows and offset. The conjecture says precisely that the irreducible row indices are the members of A069353. The [official A069353 export](https://github.com/oeis/oeisdata/blob/e80c38cadbb935f549ca291ffa8fda702a3ff278/seq/A069/A069353.seq) defines that set as the integers 2^a 3^b−1 for a,b≥0. Its separate question about infinitely many primes is unrelated to this project.

Thus, with P_n denoting the source row polynomial, the intended classification is

\[
\operatorname{Irreducible}_{\mathbb Q}(P_n)
\quad\Longleftrightarrow\quad
\exists a,b\in\mathbb N,\ n+1=2^a3^b.
\]

There is an explicit off-by-one error in the entry's descriptive title: it calls row n a degree-n polynomial. The program and every displayed row have degree n+1, starting with P_0=X−2. The theorem must follow the program, displayed polynomials, and zero-based derivative order. Correcting that descriptive mismatch is not a separate conjecture resolution.

The first displayed rows are P_0=X−2, P_1=−X²+4X−1, P_2=X³−6X²+3X+1, and P_3=−X⁴+8X³−6X²−4X+2. The first reducible row is n=4, whose printed factorization has the linear factor X+1, consistent with N=n+1=5.

## Exact algebraic connection

The following is our derivation from the source rational function, rather than a quotation from the references. Let u=(1+i√3)/2, v=1−u, α=u−X, β=v−X, and N=n+1. Then D=X²−X+1=αβ, and partial fractions give

\[
P_n=-v\alpha^N-u\beta^N
   =(-1)^{N+1}v\big((X-u)^N-v(X-v)^N\big).
\]

The identities v²=−u and u+v=uv=1 determine the sixth-root phase; conjugation exchanges u and v. In particular, the binomial after the fractional-linear substitution is Y^N−v. The formal field is the quotient of ℚ[Y] by Y²−Y+1, so the proof needs no analytic interpretation of the complex numbers used here for notation.

For N=2^a3^b, its quadratic norm is the classical cyclotomic polynomial

\[
Y^{2N}-Y^N+1=\Phi_{6N}(Y).
\]

If p>3 is a prime divisor of N=pM, select c∈{1,5} with cp≡1 mod 6. Then α^M−v^cβ^M divides α^N−vβ^N. This is the source row of degree M when p≡1 mod 6 and its reflection under X↦1−X when p≡5 mod 6, up to nonzero scalars. These are the two directions of the completed formal classification. The cyclotomic identity and fractional-linear method themselves are classical ingredients and are not claimed as new theorems of algebra.

## Closest exact-family literature

### Remete's generalized simplest polynomials

Primary source: L. Remete, [A generalization of simplest number fields and their integral basis](https://arxiv.org/abs/2111.08341), arXiv:2111.08341v1, November 16, 2021; [primary PDF](https://arxiv.org/pdf/2111.08341).

Section 2 defines f_m^(N)(Y)=Σ_j binom(N,j)Y^j g(N−j), where the six-periodic g has values (1,−m,−m−1,−1,m,m+1). Comparing coefficients or the partial-fraction expression gives the exact specialization

\[
P_{N-1}(X)=(-1)^{N+1} f_1^{(N)}(X-1).
\]

This exact-family identification is our derivation: at m=1, g(k)=u^(k+1)+v^(k+1), so the binomial theorem gives f_1^(N)(Y)=u(Y+u)^N+v(Y+v)^N, which agrees with the displayed source closed form after Y=X−1 and the indicated sign. It means the underlying all-degree polynomial family is already in the literature. The paper also develops its derivative rule and fractional-linear root symmetries.

The complete irreducibility subsection 2.2 was read, together with the family definitions and the relevant later assumptions. Corollary 10 proves a sufficient criterion: some prime p≠3 must satisfy v_p(m²+m+1)=1. For m=1, m²+m+1=3, so that criterion does not apply. The subsection explicitly restricts its aim to a sufficient condition. No complete m=1 degree classification was located in the inspected paper. That absence is a bounded finding, not a claim that no prior theorem could imply it.

### Generalized Rikuna specializations

Primary source: C. Cass, J. Cullinan, A. Rasmussen and D. Trifunovski, [Specializations of Generalized Rikuna Polynomials](https://homepages.math.uic.edu/~dtrifu2/pdf/rikuna_spec.pdf), author-hosted preprint; published in International Journal of Number Theory 10(3), 2014, pages 585–600, DOI 10.1142/S1793042113501108.

The definitions, setup, and relevant portions of Sections 4 and 5 were inspected. The paper treats iterates for a fixed odd prime ℓ over the field containing ζ_ℓ+ζ_ℓ^−1, with degree ℓ^n. It analyzes reducible specializations and root-of-unity specializations; some cyclotomic conclusions explicitly assume irreducibility. These are close prior instances of the fractional-linear/cyclotomic method. The inspected sections do not state the mixed 2^a3^b degree classification for the A327315 derivative family. No assertion of having checked every theorem in this paper is made.

### Tangent analogues of Chebyshev polynomials

Primary source: J. S. Calcut, [The Tangent Analogues of the Chebyshev Polynomials](https://www2.oberlin.edu/faculty/jcalcut/arctan.pdf), dated November 10, 2008.

The definitions and relevant rational/square-root-of-three angle discussion were inspected. Calcut studies Im(1+iX)^n and Re(1+iX)^n, their tangent identities, and factorization through angle minimal polynomials. This is prior cyclotomic-angle factorization work. A327315 additionally has a sixth-root phase and a √3 change of scale, so rational irreducibility cannot be transferred from the unscaled tangent family without a separate argument. No exact A327315 classification was located in the inspected sections.

## Bounded public search

Both available web-search engines were used. Queries included the exact identifier with proof, proved, resolved, irreducibility, and cyclotomic; Kimberling with the literal rational function; generalized simplest polynomials at m=1; Rikuna specializations; and tangent/cotangent polynomials with 2^a3^b degrees. The current trureturing conjecture catalog was opened and searched for A327315. Public GitHub issue searches in the-omega-institute/trureturing and google-deepmind/formal-conjectures returned no A327315 matches. Saved issue results are in `prior_search/`.

Because related older work can omit the identifier, targeted GitHub code searches were also run. The exact A327315 query in VladimirReshetnikov/ProveIt returned no results. Its semantic searches for Kimberling irreducibility, Rikuna/Remete/generalized simplest, and the literal denominator produced no relevant classification; denominator matches concerned unrelated trinomial/polylogarithm rigidity. The broader cyclotomic/smooth/irreducible query was noisy and cannot be treated as exhaustive coverage. Global A327315 results consisted of sequence-generation code, this project's previous source snapshots, and irrelevant substring collisions. Global A069353 results concerned implementations and other sequence references. The returned records are preserved as `github_code_*.json` and `github_code_more_*.json`; the indexed ProveIt result snapshot was commit `cb0cb077fdaed91ea722783ba2b61d60973b7f18`.

Search terms and the bounded returned result sets do not prove absence of prior publication. The appropriately qualified claim is: the explicit OEIS classification was still recorded as conjectural in the checked source, and no earlier proof of that exact classification was located in the sources inspected. This package credits the exact Remete family and the older cyclotomic/Möbius methods; reused ingredients and the source's degree typo are not counted as additional resolutions.
