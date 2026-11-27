# A universal 3-adic limit for Fibonacci–Collatz sequences

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

A complete written and Lean-checked proof of Giovanni Resta's residue-stabilization conjectures in **[OEIS A105801](https://oeis.org/A105801)** and **[OEIS A181717](https://oeis.org/A181717)**. The proof establishes a stronger theorem for every pair of distinct nonnegative starting values and identifies the exact stabilized residue.

## The theorem

Start with nonnegative integers $a_1=x$, $a_2=y$, and define

$$
a_{n+2}=\begin{cases}
(a_n+a_{n+1})/2,&a_n+a_{n+1}\text{ even},\\
3(a_n+a_{n+1})+1,&a_n+a_{n+1}\text{ odd}.
\end{cases}
$$

If $x\ne y$, then

$$
\boxed{\forall k\ge0,\ \exists N_k,\ \forall n\ge N_k:
\quad 3^k\mid5a_n+1.}
$$

In particular, all sufficiently late terms have the same residue modulo $3^k$, independently of the starting pair:

$$
a_n\bmod3^k=r_k,
\qquad
r_k=\left\lfloor\frac{(2^k\bmod5)\,3^k}{5}\right\rfloor.
$$

The formal proof also establishes

$$
0\le r_k<3^k,\qquad
5r_k+1=(2^k\bmod5)\,3^k.
$$

Thus the residue is precisely $-5^{-1}\pmod{3^k}$. Equivalently,

$$
\boxed{a_n\longrightarrow-\frac15\quad\text{in the 3-adic metric}.}
$$

This means that increasingly many trailing base-3 digits eventually become permanent. The compatible digits are $\cdots01210121_3$. The formal theorem uses natural-number congruences directly; the 3-adic statement is their mathematical interpretation, without a separate formalization using Lean's topological `Padic` type.

The initial pairs $(1,2)$ and $(0,1)$ give A105801 and A181717, respectively. If the two starting values are equal, the sequence stays constant at that value.

## Why the argument works

Set $b_n=5a_n+1$. The recurrence becomes

$$
b_{n+2}=\frac{b_n+b_{n+1}}2
\quad\text{or}\quad
b_{n+2}=3(b_n+b_{n+1}),
$$

with the same parity decision as the original recurrence.

1. **Unequal adjacent terms remain unequal.** During an averaging step, their positive absolute difference is halved. Therefore an infinite tail of averaging steps is impossible.
2. **Pairs of expansion steps recur.** After a finite initial segment, no two odd terms are adjacent. Odd terms occur arbitrarily late, and each one has an even predecessor and forces two consecutive expansion steps. The proof includes the extra descent argument needed when both starting terms are odd.
3. **Divisibility is preserved.** If two adjacent $b$ terms are divisible by $3^k$, every later $b$ term is too. Division by 2 preserves this because 2 is coprime to $3^k$.
4. **Two expansion steps increase the power.** Both newly produced terms become divisible by $3^{k+1}$. Induction on $k$ proves the theorem, and cancellation of 5 identifies the exact residue.

This is an argument for all natural indices and all exponents, with no finite-state extrapolation or assumed pattern in the parity sequence.

## Examples

These use the OEIS convention that the supplied seeds have indices 1 and 2. Each $N$ is the first pair of consecutive terms in the specified residue class; the proved persistence lemma makes the entire tail from $N$ stable.

| $k$ | Modulus $3^k$ | Stable residue $r_k$ | $N$ for A105801 | $N$ for A181717 |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 1 | 6 | 2 |
| 2 | 9 | 7 | 10 | 7 |
| 3 | 27 | 16 | 13 | 10 |
| 4 | 81 | 16 | 15 | 15 |
| 5 | 243 | 97 | 19 | 19 |
| 6 | 729 | 583 | 22 | 23 |
| 7 | 2187 | 1312 | 24 | 25 |
| 8 | 6561 | 1312 | 28 | 30 |

The finite example calculations are reproduced by `python examples.py`. They illustrate the general theorem and are not premises of the formal proof.

## Files

| File | Purpose |
| --- | --- |
| [A105801_A181717_proof.pdf](A105801_A181717_proof.pdf) | Complete mathematical proof, explicit residues, examples, and relation to earlier work. |
| [A105801_A181717_proof.tex](A105801_A181717_proof.tex) | Editable LaTeX source. |
| [Proof.lean](Proof.lean) | Complete formal proof of the general theorem and both named OEIS conjectures. |
| [lean-toolchain](lean-toolchain), [lakefile.lean](lakefile.lean), [lake-manifest.json](lake-manifest.json) | Lean 4.19.0 pin and dependency-free project configuration. |
| [verification.txt](verification.txt) | Successful fresh package build and axiom reports. |
| [AUDIT.md](AUDIT.md), [audit-verification.txt](audit-verification.txt) | Separate mathematical/source review and independent rebuild. |
| [examples.py](examples.py), [examples.txt](examples.txt) | Reproducible example residues and onset indices. |
| [SHA256SUMS.txt](SHA256SUMS.txt) | Checksums of the complete package. |

## Reproduce the formal verification

With Lean managed by Elan, run from this directory:

```sh
lean Proof.lean
```

Or build the supplied project:

```sh
lake build
```

The single source imports **only `Std`**. There is no Mathlib or other external dependency to download.

The general theorem is:

```lean
theorem FibonacciCollatz.eventual_residue
    (s : Nat × Nat) (hne : s.1 ≠ s.2) (k : Nat) :
    ∃ N, ∀ n, N ≤ n →
      FibonacciCollatz.sequence s n % (3 ^ k) =
        FibonacciCollatz.stableResidue k
```

The two specific conjectures have no unproved hypotheses:

```lean
theorem A105801.conjecture (k : Nat) :
    ∃ N, ∀ n, N ≤ n →
      A105801.a n % (3 ^ k) = FibonacciCollatz.stableResidue k

theorem A181717.conjecture (k : Nat) :
    ∃ N, ∀ n, N ≤ n →
      A181717.a n % (3 ^ k) = FibonacciCollatz.stableResidue k
```

The source explicitly proves the initial values and the original recurrence for each sequence. Their unused value at index 0 is set to 0.

The packaged source passed a fresh build. All reported final theorems depend only on the standard logical axioms:

```text
[propext, Quot.sound]
```

There are no unfinished proofs, custom axioms, `native_decide` calls, unsafe declarations, or replacement implementations.

To rebuild the paper with a standard TeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error A105801_A181717_proof.tex
pdflatex -interaction=nonstopmode -halt-on-error A105801_A181717_proof.tex
```

## Attribution and earlier work

The retrieved OEIS entries attribute both arbitrary-power stabilization conjectures to **Giovanni Resta, November 17, 2010**. A105801 was contributed by Zak Seidov on September 12, 2006; A181717 by Ralf Stephan on November 17, 2010. Both entries already record the simpler eventual residue 7 modulo 9.

Two related sources deserve explicit credit:

- **John Greene**, [*The Unboundedness of a Family of Difference Equations Over the Integers*](https://www.fq.math.ca/Papers1/46_47-2/Greene_1-09.pdf), *The Fibonacci Quarterly* 46/47(2), 2008/2009, pp. 146–152. Our affine transformation places the sequence in Greene's family with coefficients $c_1=c_2=3$ and divisor $d=6$. His theorem gives ordinary divergence for unequal positive transformed seeds. The present target is eventual stabilization modulo every power of 3 and identification of the 3-adic limit; ordinary divergence is not claimed as new.
- A [2025 Math.StackExchange discussion](https://math.stackexchange.com/questions/5028237/) of the A181717 digital-root pattern includes Blue's observation that two consecutive terms congruent to 7 modulo 9 force all following terms to remain in that residue class.

The retrieved OEIS entries still label the all-powers assertions as conjectures. Searches by exact identifier and equivalent recurrence, including the related literature and available proof collections, did not locate an earlier proof of those assertions. The audit records the search scope and retrieval limitations. This does not establish exhaustive publication priority or imply that OEIS has reviewed or accepted this proof.
