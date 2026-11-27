# Balanced two-column arrays

For any ordered alphabet of $q\ge2$ letters, count weakly increasing two-column arrays of height $n$ whose letter multiplicities differ by at most one. We give a formula valid at every height. It is a quasipolynomial of degree $q-1$ and **least quasiperiod $q$**. We determine its leading coefficient on every residue class. For odd $q$, the reduced generating-function denominator is exactly $(1-x^q)^q$.

For alphabet sizes 3 through 8, the formula proves all 33 residue polynomials listed by R. H. Hardin. For these three even alphabet sizes the least denominator is $(1-x^{q/2})(1-x^q)^{q-1}$. The coefficients table expresses each constituent as a sum of integer multiples of binomial coefficients. [A201271](https://oeis.org/A201271) · [A201445](https://oeis.org/A201445) · [A200984](https://oeis.org/A200984) · [A201136](https://oeis.org/A201136) · [A201066](https://oeis.org/A201066) · [A201095](https://oeis.org/A201095)

[Manuscript](balanced-arrays.pdf) · [LaTeX source](balanced-arrays.tex) · [33 polynomials](coefficients.csv) · [Exact verifier](verify.py)

Run `python3 verify.py`. It checks the bridge formula against direct array counts, verifies every coefficient by finite differences, and reduces all six exact denominators.
