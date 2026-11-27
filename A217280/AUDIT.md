# Independent audit of A217280

The complete final `Proof.lean`, README, and included official OEIS source record were read. The exact Lean source was copied to an isolated audit directory and compiled afresh with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Compilation returned exit code 0. The four printed public theorems report only `propext`, `Classical.choice`, and `Quot.sound`. The command, output, and final hash are recorded in `audit-verification.txt`.

## Original statement and definitions

The source's finite sum is literally the Lean definition:

\[
a(n)=\sum_{k=0}^{n}\binom nk^3 2^k3^{n-k}.
\]

The target uses the standard remainder `a n % 5` and the standard digit list `Nat.digits 5 n`. Its allowed-digit predicate quantifies over every digit and requires each to be 0 or 2. The index n=0 is included: the digit list is empty, so the predicate holds, and the original sum is a(0)=1. This is consistent with the ordinary representation of zero and with the source's listed exceptional positions.

The theorem gives the complete dichotomy, not only a necessary condition or a finite verification. It proves remainder 1 at every permitted index and remainder 0 at every other index.

## Lucas decomposition

The application of Lucas's theorem correctly splits both the upper and lower indices into quotient and remainder modulo 5. The proof separately handles the branch s>r: the small binomial coefficient is zero modulo 5, so the whole term vanishes. It does not incorrectly subtract base-five digits across a borrow.

In the branch s<=r and j<=q, the equality

\[
5q+r-(5j+s)=5(q-j)+(r-s)
\]

is valid over natural numbers. The weights then split using x^5=x in `ZMod 5`. Cubing the factored binomial coefficient gives the product of the two smaller weighted summands.

The padding step is also exact. The original range 0<=k<=5q+r is extended to 0<=k<5(q+1), and every added term is zero because its ordinary binomial coefficient vanishes. These terms remain zero even though natural subtraction in the unused exponent is truncated. Splitting the padded interval into complete blocks produces precisely 0<=j<=q and 0<=s<5. The latter sum reduces to a(r) because terms with s>r vanish.

Consequently the proved one-digit identity is

\[
a(5q+r)\equiv a(q)a(r)\pmod5.
\]

The five seed residues are exactly 1,0,1,0,0. Their computations use ordinary kernel-checked `decide`, not `native_decide`. Strong induction on n uses n/5<n for positive n and the standard digit-cons identity to establish the full classification.

## Conclusions and scope

`A217280.conjecture` proves the exact natural-number remainder formula at every n. `one_iff` and `divisible_iff` correctly extract the two equivalent source formulations. There is no assumed alternate sequence, no unproved digit bridge, no additional hypothesis on n, and no omitted range of indices.

The README proof agrees with the checked argument, including the incomplete-block padding and the s>r case. Its initial values and examples are correct. The classical Lucas/Fermat method is explicitly credited as prior mathematics; the package claims the specific OEIS classification, not a new general congruence theorem. Broader priority findings are limited to the separate searches recorded by the author.

No defect, placeholder, custom axiom, unsafe proof replacement, or source-definition mismatch was found.

Checked source SHA-256:

`831c7287cf161b648658c32f6b61945e2259c2206c37b44720a06d4e6c106c45`
