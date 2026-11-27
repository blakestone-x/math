# A073642: the squared-valuation identity and an asymptotic correction

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Statement and source

Write an integer n >= 0 in binary as n = sum_j epsilon_j 2^j,
with epsilon_j in {0,1}. Let

$$
s_2(n)=\sum_j\epsilon_j,
\qquad
a(n)=\sum_jj\epsilon_j.
$$

The second function is OEIS A073642. Let nu_2(k) be the exponent of 2
in the prime factorization of k, for k >= 1. Velin Yanev's September 9,
2017 conjecture is

$$
a(n)=\frac{3\bigl(n-s_2(n)\bigr)-\sum_{k=1}^n\nu_2(k)^2}{2}.
$$

The OEIS writes n-s_2(n) as A011371(n) and nu_2(k) as A007814(k).
The entry still marks this identity as a conjecture. We prove it for
every n >= 0, including its zero case.

Primary sources:

- <https://oeis.org/A073642/internal>, revision 121, July 5, 2026.
- <https://oeis.org/A011371/internal>, the definition n-s_2(n).
- <https://oeis.org/A007814>, the binary valuation.

## Proof by binary carries

Fix k >= 1 and set t=nu_2(k). When k-1 is incremented to k, its t
trailing one-bits, in positions 0,...,t-1, become zero and its bit in
position t becomes one. Higher bits are unchanged. It follows that

$$
s_2(k)-s_2(k-1)=1-t,
$$

and

$$
a(k)-a(k-1)
=t-\sum_{j=0}^{t-1}j
=\frac{3t-t^2}{2}.
$$

Thus

$$
2\bigl(a(k)-a(k-1)\bigr)
=3\nu_2(k)-\nu_2(k)^2.
$$

Summing the first increment equation from 1 through n gives

$$
\sum_{k=1}^n\nu_2(k)=n-s_2(n).
$$

Summing the second equation gives

$$
2a(n)=3\sum_{k=1}^n\nu_2(k)
-\sum_{k=1}^n\nu_2(k)^2.
$$

Substitution proves the conjecture. In particular, its numerator is
always nonnegative and even; the displayed division is exact.

## Equivalent subtraction-free identity

The machine proof first establishes the following identity over the
natural numbers, which avoids subtraction entirely:

$$
2a(n)+\sum_{k=1}^n\nu_2(k)^2+3s_2(n)=3n.
$$

For the local carry argument it proves the two increment equations
simultaneously by strong induction, splitting n into even and odd
cases. The binary recursions are

$$
s_2(2m)=s_2(m),\quad s_2(2m+1)=s_2(m)+1,
$$

$$
a(2m)=a(2m+1)=a(m)+s_2(m),
$$

$$
\nu_2(2m)=\nu_2(m)+1\ (m>0),\quad \nu_2(2m+1)=0.
$$

These are direct consequences of binary notation and valuation. The
recurrences for a(n) and s_2(n) are also already recorded in the OEIS
entry, attributed to Ralf Stephan in 2003; they are used as known
descriptions, not claimed as new results.

## Formal verification and exact definitions

The source file `Proof.lean` proves both the subtraction-free
identity and the stated divided formula. It additionally proves bridges
from the computational binary recursions to mathlib's standard
`Nat.digits 2 n` and from the recursive valuation to
`padicValNat 2 n`. A positional digit-weight function literally sums
the digits multiplied by their zero-based positions. The final theorem
`A073642.oeis_conjecture` is therefore expressed with the standard
binary-digit list and standard 2-adic valuation, with a finite sum over
the integers 1 through n.

The file was checked with Lean 4.19.0 and mathlib v4.19.0, commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Its imports are
`Mathlib.Tactic.Linarith`, `Mathlib.Tactic.NormNum`, and
`Mathlib.NumberTheory.Padics.PadicVal.Basic`.
The final theorem depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. There are no placeholders, added
axioms, or `native_decide` uses.

## Prior work and search limits

On November 26, 2026 the OEIS still labels Yanev's identity conjectural.
The entry's references
to MacDonald's 1971 representation-theoretic work and Ayyer, Prasad,
and Spallone's 2016 work concern the partition interpretation of a(n).

Exact-ID and semantic searches for the weighted binary-digit and
squared-valuation identity, plus targeted checks for public
trureturing, Fabian Arevalo, and Eppie material, found no prior proof
of this particular statement. The conclusion is limited to those
searches; it is not a claim of exhaustive historical novelty.

## A separate asymptotic assertion in the same entry

The entry also suggests that the summatory function is asymptotic to
`C n log(n)^2`, with `0.47 < C < 1/2`. With `log` interpreted as the
natural logarithm, that proposed range is false. This is an additional
resolved assertion in **the same OEIS entry**, not another sequence.

Write

$$
S(n)=\sum_{k=1}^n a(k).
$$

Among the integers from 0 through 2^m-1, each of the m bit positions is
set exactly 2^(m-1) times. Since a(2^m)=m, this gives the exact identity

$$
4S(2^m)=2^m m(m-1)+4m.
$$

For m >= 1, division by 4 times the natural-log normalization gives

$$
\frac{S(2^m)}{2^m\log(2^m)^2}
=\frac{1-1/m}{4\log(2)^2}
+\frac{2^{-m}}{m\log(2)^2}.
$$

Therefore

$$
\lim_{m\to\infty}\frac{S(2^m)}{2^m\log(2^m)^2}
=\frac{1}{4\log(2)^2}\approx0.5203422453>\frac12.
$$

The strict comparison is also formally checked. A four-degree Taylor
lower bound for exp(7/10) proves exp(7/10)>2, hence log(2)<7/10.
Since log(2)>0, its square is less than 49/100<1/2, which implies the
displayed constant is greater than 1/2.

If the full normalized summatory sequence had a limit C, its
power-of-two subsequence would have the same limit. Uniqueness of limits
therefore forces C=1/(4 log(2)^2), ruling out every C<1/2 and in
particular the proposed interval. This argument **does not assert or
formalize existence of the full all-index limit**. The checked result
is the power-of-two limit and the consequent exclusion of the stated
global constant range.

`Asymptotic.lean` proves the exact block identities, the real subsequence
limit (`power_two_limit`), the strict bound (`leadingConstant_gt_half`),
and the exclusion theorem (`no_limit_below_half`). It imports the same
`Proof.lean`, so all sequence definitions are shared. The block-counting
method is elementary; this result is presented as a correction of the
specific OEIS assertion, not as a new general theory of weighted digit
sums.


## Reproduce the verification

From this directory, using Elan to select the pinned Lean toolchain, run:

```sh
lake exe cache get
lake build
```

`lakefile.lean` pins mathlib to its v4.19.0 commit, and
`lake-manifest.json` locks its transitive dependencies. The package
includes `verification.txt` from a fresh build of these exact sources,
plus an independent review in `AUDIT.md` and `audit-verification.txt`.
No network access is needed after the dependency source and compiled
cache have been obtained.

## Collected proof document

[Read the complete proof collection (PDF)](../notes/Math_Proofs_Batch4.pdf) · [LaTeX source](../notes/Math_Proofs_Batch4.tex)
