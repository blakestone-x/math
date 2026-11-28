# A291897: squares dividing Euler-polynomial numerators

For every positive integer `n`, this package proves

\[
(2n-1)^2\mid\operatorname{num}\bigl(E_{2n-1}(n)\bigr),
\]

where `num` is the numerator after reducing the rational number to lowest terms. This is the square-divisibility conjecture recorded in [OEIS A291897](https://oeis.org/A291897), authored by Vladimir Shevelev in 2017. The proof covers every positive index.

## Proof

Let `e_m` be the signed Euler numbers `1,0,-1,0,5,0,-61,...`. The classical centered expansion gives the integer polynomial

\[
P_m(x)=\sum_{j=0}^{m}\binom mj e_{m-j}x^j
      =2^m E_m\!\left(\frac{x+1}{2}\right).
\]

Suppose `m` is odd and `m` divides the integer `x`. The constant term is zero because `e_m=0`. The linear term is `m e_(m-1) x`, so it is divisible by `m²`. Every remaining term contains `x²` and is therefore also divisible by `m²`. Thus `m²` divides `P_m(x)`.

The denominator `2^m` is coprime to the odd number `m²`, so reducing `P_m(x)/2^m` cannot remove that divisor from its numerator. Set `m=x=2n−1` to obtain the conjecture.

The generalized multiple-of-degree theorem is part of the same mathematical family. It is not counted as another solved problem. The neighboring cubic-divisibility assertion in A292911 is outside this package.

## Formal statement and boundary

[EulerSource.lean](EulerSource.lean) defines the signed Euler numbers by their classical integer recurrence, the centered finite expansion, rational Euler values, and the actual reduced numerator. [EulerProof.lean](EulerProof.lean) proves:

- `square_dvd_centered`: `m²` divides the centered value for odd `m` and `m ∣ x`;
- `odd_square_dvd_num`: the divisibility survives rational reduction;
- `source_conjecture`: the exact A291897 assertion for every `n>0`.

The finite expansion is the formal definition of the Euler value. Its identification with the usual exponential-generating-function convention is explained in the manuscript using the classical [NIST DLMF formulas](https://dlmf.nist.gov/24.2#E10). A separate analytic generating-function equivalence is not formalized in this package.

## Reproduction and evidence

Run `lake build` with Lean 4.19.0. The package pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and includes the full dependency manifest. Both local modules are explicit default build roots.

[verification.txt](verification.txt) and [independent_build.log](independent_build.log) record separate fresh source-only builds, exact input hashes, and the printed axiom audits. The independent build uses a separate local build directory; both builds use the same pinned compiler and external dependency caches. The audited theorems depend only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. No local admissions, custom axioms, or `native_decide` are used.

[verify.py](verify.py) provides supplementary exact-arithmetic checks: all 15 frozen source terms, comparison with independently computed Euler polynomials through degree 12, the source assertion through `n=100`, and the generalized theorem for odd degrees through 25 at several positive and negative multiples. These finite checks supplement the unbounded Lean proofs.

## Sources and attribution

The signed Euler recurrence and centered expansion are classical. The existing admitted statement in `GuillaumeBAUD-coder/open-math-agents` uses the same source representation and credits `@DhruRules`; that source formalization is acknowledged, while its unfinished assertion is proved here without importing that file. Shevelev's linked 2017 paper concerns a different Euler-polynomial denominator question. Carlitz's 1954 paper supplies related classical Euler formulas and congruences.

[source_checks.md](source_checks.md) records the bounded prior-work screening and precise scope. It does not establish worldwide priority. The selected OEIS entry and neighboring entry are frozen with immutable URLs and SHA-256 hashes in [sources/manifest.json](sources/manifest.json). A complete human proof is in [manuscript-section.tex](manuscript-section.tex) and the Batch 16 manuscript.
