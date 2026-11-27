# A326925: source and prior-result check

Checked independently on November 27, 2026. This is a bounded prior-publication check, not a certification of historical priority.

## Original statement

The official OEIS export A326925, revision 13, October 31, 2019, has Git blob SHA `e8036d79dbacfa38c832486936d3d80b5472cde1`. The preserved `A326925.seq` was verified against this hash. It records two clauses: odd-degree polynomials are irreducible; even-degree polynomials of degree 2k have exactly two irreducible factors of degree k. The current audit target is the **odd-degree clause**.

The source title has an index mismatch: the zeroth derivative of `(1-x)/(1-x-x²)` has numerator of degree 1, not degree 0. The displayed polynomials and Mathematica program make the intended order unambiguous. With `P₁=1-x`, the nth derivative is `n! Pₙ₊₁/(1-x-x²)ⁿ⁺¹`, before harmless scalar/sign normalization. Thus odd polynomial degree corresponds to even derivative order. The program's `(-1)^(n+1)` sign normalization does not affect irreducibility over the rationals. This indexing issue is not a separate assertion resolved.

Primary locations:

- https://oeis.org/A326925
- https://github.com/oeis/oeisdata/blob/main/seq/A326/A326925.seq

## Related official entries

The complete official records A328610 and A328611 were also read and preserved. Their definitions repeat the even-degree factor conjecture, and they contain no proof link for either irreducibility clause. Their derivative-index wording repeats the same mismatch; their explicit factor lists and executable loops clarify the intended degree indexing.

| Entry | Revision | Git blob SHA |
|---|---|---|
| A328610 | 12, October 31, 2019 | `91e469434417481063f3629100c931cc3d2fdce0` |
| A328611 | 11, October 31, 2019 | `273ca073f7b24d3ff7ccb59d92f72e14ba0ce7ea` |
| A327315 | 6, November 6, 2019 | `47efe5bcf666241a43536ea4f106e7342c741f96` |

A327315 is a different rational function and a different irreducibility classification. Its conjecture is not covered by the odd-degree theorem under audit. The companion references A094440 and A094441 were read in full: they give related Fibonacci/binomial row polynomials, known formulas, and different derivative numerators. Neither checked record contains a proof of the A326925 irreducibility assertion.

## Search-engine and resolved-index checks

Both available search engines were used for exact and semantic queries, including:

- `"A326925" irreducible proof`
- `"A326925" "odd"`
- `"A326925" proof irreducibility`
- `"derivative" "Fibonacci" "irreducible" polynomials Kimberling`
- `"Fibonacci" "Appell" "irreducible"`
- `"Fibonacci" "binomial" "polynomials" "odd" "irreducible"`
- `"Fibonacci Jensen polynomials" irreducible`
- `"A094440" irreducible`
- `"A094441" irreducible`

The exact hits reproduced the conjecture or related OEIS records. No earlier proof of the specific odd-degree derivative-numerator assertion was located. The live trureturing index returned no match for A326925, A327315, or “derivative polynomial”; semantic hits for Kimberling concerned unrelated word, array, and numeration problems.

## Nearby literature examined

Dan Levy's *The irreducible factorization of Fibonacci polynomials over Q*, Fibonacci Quarterly 39 (2001), 309–319, was opened at its primary journal URL:

https://www.fq.math.ca/Scanned/39-4/levy.pdf

Its stated families are the standard Fibonacci, Lucas, and Chebyshev-type polynomials satisfying recurrence `yₙ₊₁=x yₙ+b yₙ₋₁` for constant `b=±1`. Its prime-degree/cyclotomic factorization result is not the same polynomial family or odd-degree assertion as A326925. The present argument uses classical binomial irreducibility; no new general irreducibility criterion is claimed.

The primary author copy of Navas–Ruiz–Varona, *Appell polynomials as values of special functions*, J. Math. Anal. Appl. 459 (2018), 419–436, was also opened:

https://investigacion.unirioja.es/documentos/5bbc68beb750603269e80ebc/f/6297af03452cef25807f7ed0.pdf

The Fibonacci discussion in section 4.8 concerns a renormalized Appell–Lerch generating function and special-function values, with a different polynomial family. No irreducibility statement was found in the retrieved paper. Search results for standard Fibonacci-polynomial derivatives, Fibonacci–Appell variants, and golden-calculus polynomial families therefore were not treated as resolutions of A326925.

An unchanged source conjecture label alone does not establish that a question remains open in all unindexed or unpublished work. The supported conclusion is that the exact source clause survives these explicit checks and has a complete proposed formal proof, with historical priority left qualified.
