# A217280: a base-five digit classification

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## The conjecture

Paul D. Hanna's OEIS A217280, introduced September 29, 2012, is

$$a(n)=\sum_{k=0}^{n}\binom nk^{\!3}\,2^k3^{n-k},\qquad n\ge0.$$

The entry conjectures that the remainder modulo five is always zero or
one, and is one precisely when the base-five representation of the index
uses only the digits zero and two. We prove the complete assertion:

$$
a(n)\equiv
\begin{cases}
1\pmod5,&\text{every base-five digit of }n\text{ is }0\text{ or }2,\\
0\pmod5,&\text{otherwise}.
\end{cases}
$$

The convention at zero is harmless: its usual representation is `0`, and
Lean's `Nat.digits 5 0` is empty; both satisfy the digit condition and
a(0)=1.

Primary source: <https://oeis.org/A217280>.
The included `source.seq` is the official OEIS data export, revision 25,
July 27, 2022, retrieved November 26, 2026. It still describes this assertion
as a conjecture. Its SHA-256 is
`c747b32641cd82f9dfcfd460e83376830b3152d4373c8d158959d20152daf637`.

## Proof

Write n=5q+r, with 0≤r<5. Decompose a summation index as k=5j+s,
with 0≤s<5. Lucas's theorem gives

$$\binom{5q+r}{5j+s}\equiv\binom qj\binom rs\pmod5.$$

If s>r, the second binomial coefficient vanishes, so the whole summand
is zero modulo five. If s≤r and j≤q, there is no borrow in the subtraction:

$$5q+r-(5j+s)=5(q-j)+(r-s).$$

Fermat's congruences 2^5≡2 and 3^5≡3 modulo five therefore give

$$
\binom{5q+r}{5j+s}^{\!3}2^{5j+s}3^{5q+r-5j-s}
\equiv
\left(\binom qj^{\!3}2^j3^{q-j}\right)
\left(\binom rs^{\!3}2^s3^{r-s}\right)\pmod5.
$$

To avoid any issue with the last incomplete block, pad the original
summation with zero summands for k>5q+r until its range is 0≤k<5(q+1).
This avoids negative exponents in the added terms, whose binomial
coefficients are zero. The resulting rectangle 0≤j≤q, 0≤s<5 factors into two
sums; the terms s>r in the second sum vanish. Thus

$$\boxed{a(5q+r)\equiv a(q)a(r)\pmod5.}$$

The five initial values are

| r | 0 | 1 | 2 | 3 | 4 |
|---|---:|---:|---:|---:|---:|
| a(r) | 1 | 5 | 61 | 845 | 12865 |
| a(r) mod 5 | 1 | 0 | 1 | 0 | 0 |

Repeatedly removing the last base-five digit therefore expresses a(n)
modulo five as the product of the corresponding single-digit residues.
Every factor is one exactly when its digit is zero or two; any other
digit contributes a zero factor. This proves the claim for all n.

For example, 62=222 in base five has residue one. The index 63=223
has a digit three and hence gives a multiple of five.

## What is formally checked

`Proof.lean` defines the exact original finite sum over natural numbers.
It then casts that sum into `ZMod 5`, proves the padding and reindexing
steps, applies mathlib's Lucas theorem, proves the five base cases, and
uses strong induction on the index to obtain the full digit statement.
The digit predicate is defined directly with `Nat.digits 5 n`; no
unproved recurrence or alternative sequence is substituted for the
OEIS definition.

The public results include:

- `A217280.lucas_step`: the one-digit multiplicative congruence;
- `A217280.conjecture`: the exact remainder formula for every natural n;
- `A217280.one_iff`: residue one occurs exactly at the permitted indices;
- `A217280.divisible_iff`: five divides a(n) exactly at all other indices.

Lean 4.19.0 and mathlib v4.19.0, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, check the complete proof.
The reported dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`. There are no proof placeholders, additional axioms, or
`native_decide` calls.

## Prior work and scope

The argument is an elementary application of the classical Lucas
congruence and Fermat's little theorem. The general method of deriving
digitwise congruences for binomial sums is established mathematics;
we do not claim a new general Lucas theorem. The result here is a complete
proof and formalization of the specific classification still recorded
as conjectural in A217280.

The entry already contains asymptotic, hypergeometric, and linear
recurrence formulas credited to Vaclav Kotesovec, Mark van Hoeij, and
R. J. Mathar. Those statements are prior work and are not the theorem
proved here. Exact identifier and exact sequence-value searches, searches
for the weighted Franel/Lucas congruence, and checks of the public
trureturing, Fabian Arevalo, and Eppie collections did not locate an
earlier proof of the stated zero-or-two base-five classification.
This records the scope of the November 26, 2026 search, not a guarantee
of absolute priority.

Mathlib's Lucas theorem implementation, credited to Gareth Ma, is at
<https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Nat/Choose/Lucas.lean>.

## Reproduce

With the pinned Lean toolchain selected by Elan, run from this directory:

```sh
lake exe cache get
lake build
```

The lakefile pins mathlib and the manifest locks the transitive dependencies.
`verification.txt` records a fresh build of the packaged proof. The separate
`AUDIT.md` and `audit-verification.txt` record independent review and compilation.
