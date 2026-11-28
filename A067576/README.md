# A067576: eventual doubling of binary-weight columns, with the exact onset

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

This package proves Clark Kimberling's November 2025 conjecture in [OEIS A067576](https://oeis.org/A067576). Let T(i,j) be the jth positive integer, in increasing order, whose ordinary binary expansion contains exactly i ones. For every positive column j, the shifted column T(i,j)+1 eventually doubles at each new row. Its exact least starting row is

\[
\boxed{d(j)=\max(1,j-1).}
\]

The proof gives the explicit formula throughout that region:

\[
\boxed{T(i,j)+1=(2^j-1)2^{i+1-j}\qquad(i\ge\max(1,j-1)).}
\]

Thus T(i+1,j)+1 = 2(T(i,j)+1) for every i≥d(j). For j≥3 the doubling equation fails at i=j−2, so the onset cannot be moved earlier. The five initial onsets 1,1,2,3,4 agree with Kimberling's examples.

## Proof from the binary definition

Write w(n) for the number of one-bits of n, and let

\[
C_i(m)=\#\{n\in\mathbb N: n<m,\ w(n)=i\}.
\]

The binary identities w(2n)=w(n) and w(2n+1)=w(n)+1 give

\[
\begin{aligned}
C_{i+1}(2m)&=C_{i+1}(m)+C_i(m),\\
C_{i+1}(2m+1)&=C_{i+1}(m+1)+C_i(m).
\end{aligned}
\]

Binary induction also gives 2^{w(n)}≤n+1, and w(2^i−1)=i. Therefore C_i(m)=0 when m<2^i, and C_i(2^i)=1. Induction using the even-count identity yields C_i(2^{i+1})=i+1. Among the last two integers below 2^{i+1}, the integer 2^{i+1}−2 has weight i, while 2^{i+1}−1 has weight i+1. It follows that

\[
w(2^{i+1}-2)=i,\qquad C_i(2^{i+1}-2)=i.
\]

For k,d≥0, set

\[
v(k,d)=(2^{k+1}-1)2^d-1.
\]

We prove that w(v(k,d))=k+d and C_{k+d}(v(k,d))=k. The preceding identities give the base d=0. For the induction step,

\[
v(k,d+1)=2v(k,d)+1,\qquad v(k,d)+1<2^{k+d+1}.
\]

The weight increases by one, while the odd-count identity gives

\[
C_{k+d+1}(v(k,d+1))
=C_{k+d+1}(v(k,d)+1)+C_{k+d}(v(k,d))=0+k.
\]

Hence v(k,d) is precisely the (k+1)st integer of weight k+d. Taking k=j−1 and d=i+1−j proves the boxed formula. This identifies the literal increasing enumeration; no recurrence is fitted to an initial segment.

To prove sharpness, let j=k+3. The binary word

\[
u=2^{k+2}+(2^k-1)
\]

has weight k+1. Its rank is k+2: there are exactly k+2 weight-(k+1) integers below 2^{k+2}, and none with weight k below 2^k−1. Adding the leading bit at position k+2 therefore introduces no additional predecessors. Consequently

\[
T(k+1,k+3)+1=5\cdot2^k,
\qquad T(k+2,k+3)+1=2^{k+3}-1.
\]

The second value is not twice the first. Every proposed onset below j−1 would have to include this failed transition. For j=1 or j=2, the formula already starts at row 1, the least allowed positive row.

## Formal source bridge and build

`weight n` is literally `n.bitIndices.length`. The formal source entry is

```lean
Nat.nth (fun n => n.bitIndices.length = i) (j - 1)
```

For every positive row i, the proof shows the row is infinite, its entries are positive, its enumeration is strictly increasing, and its jth entry has exactly j−1 predecessors of the required weight. This covers the one-based source indices i,j≥1 and removes the total-function fallback behavior of `Nat.nth` from the mathematical statement. Row zero is used only as a convenient internal base case.

| Module | Role |
| --- | --- |
| [Binary.lean](Binary.lean) | Literal one-bit count; minimum values; exact even/odd prefix counts. |
| [Columns.lean](Columns.lean) | Source `Nat.nth` definition; exact prefix rank; closed form; eventual doubling. |
| [Sharp.lean](Sharp.lean) | Infinite rows; leading-bit count; preceding-row counterexamples; minimum onset. |
| [Proof.lean](Proof.lean) | Positive increasing source enumeration and combined theorem. |

The main endpoints are `entry_spec`, `entry_strictMono`, `entry_formula`, `eventually_geometric`, `sharp_onset`, and `full_resolution`. The endpoint `sharp_onset` uses `IsLeast`, so it proves both eventual validity and minimality.

The project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All four local modules are explicit default roots. Run:

```sh
lake exe cache get
lake build
```

The [author build](verification.txt) compiles from source and configuration copied to a fresh isolated directory, with only pinned external dependencies shared. Every principal axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. No proof source contains `sorry`, `admit`, a custom axiom, or `native_decide`.

The supplementary [integer verifier](verify.py) independently generates an 80-by-80 rectangle by successive fixed-weight binary words, validates that generator against direct enumeration below 2^16, checks all 66 displayed antidiagonal source terms, and checks 3,319 formula values, 3,239 doubling equations, and 78 sharpness counterexamples. These are transcription checks; the universal proof is in Lean.

## Attribution and scope

Robert G. Wilson v supplied the array in 2002; Kimberling supplied the eventual-doubling conjecture in 2025. The row enumeration and binary ranking methods are classical. A036563 records the diagonal special case, and A066884 records the same array with the antidiagonals reversed. Dobrić, Skyers and Stanley's [2016 paper](https://arxiv.org/abs/1603.04896), cited in A066884, develops polynomial-time weight ranking and unranking. These precedents are credited in the [source dossier](source_checks.md).

The exact minimum-onset assertion had already been formulated as a Lean statement in [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/3a0039bdf1da87d3915b73dabafd68415871f2e4/statements/oeis-a067576.lean), where its proof is left as `sorry`. We do not claim first formulation of that strengthening. This package supplies a complete proof from the literal source definition.

Both web engines and exact/semantic GitHub searches, globally and in current ProveIt/trureturing, found no earlier proof of the eventual-column assertion within the recorded bounded searches. Global historical priority remains unverified. This package counts as **one source-conjecture resolution**; the closed form, exact onset, and individual columns are components of the same result.
