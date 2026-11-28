# A134559: a counterexample to the antidiagonal-product conjecture

**Resolved by counterexample:** Lechoslaw Ratajczak's November 1, 2019 conjecture in [OEIS A134559](https://oeis.org/A134559) fails at

$$
\boxed{p=54217,\qquad (p+1)/2=27109.}
$$

Both numbers are prime. However, the antidiagonal factor at index $k=2737$ is

$$
b_{54217}(2737)=162651=3\cdot54217.
$$

It follows that $\gcd(P(54217),54217)=54217$, whereas the conjecture requires this gcd to be 1.

Blake Stone, developed with OpenAI Astra 6.2, November 27, 2026.

## The exact original statement

The source first defines

$$
b_n(k)=\sum_{\substack{1\le u\le n\\ n\bmod u=k}}u,
\qquad
P(n)=\prod_{k=0}^{\lceil n/2\rceil-1}b_n(k).
$$

These sums are the antidiagonals of the divisor triangle
$T(m,j)=\sum_{d\mid m,\,d\ge j}d$: $b_n(k)=T(n-k,k+1)$.
The conjecture identifies the positive integers satisfying

$$
\gcd(P(n),n)=1,
\qquad
\gcd(P(n+1),n+1)=2
$$

with [A005383](https://oeis.org/A005383), excluding 3 and 5: the primes $p>5$ for which $(p+1)/2$ is prime. The checked counterexample belongs to this prescribed prime family and violates the first required equation. No value of the second gcd can repair that failure.

## Proof

If $54217\bmod u=2737$, then $u>2737$, and

$$
54217=q u+2737,
\qquad qu=51480.
$$

Thus $u$ is a divisor of $51480$ greater than $2737$. Conversely, every such divisor gives the required remainder. Since $u\ge2738$, the positive quotient $q$ is at most 18. Checking the divisors among these 18 possible quotients gives exactly the following 14 values of $u$:

$$
\begin{gathered}
2860,3432,3960,4290,4680,5148,5720,6435,\\
8580,10296,12870,17160,25740,51480.
\end{gathered}
$$

Their sum is $162651=3\cdot54217$. The factor occurs in the product because
$0\le2737<\lceil54217/2\rceil=27109$. Consequently $54217\mid P(54217)$, giving the asserted gcd. Trial division proves that both $54217$ and $27109$ are prime; the Lean proof checks these primality facts with proof-producing `norm_num`.

This is a finite counterexample to the whole proposed equivalence. It does not claim that 54217 is the smallest counterexample, describe all counterexamples, or establish whether the implication in the other direction is valid.

## Formal verification

`Proof.lean` starts with the literal remainder sum over $1\le u\le n$ and the original finite product. It proves completeness of the 14-element remainder fiber using the quotient bound, computes its sum, proves both primality claims, and derives the failure of the full characterization. The enormous full product is never evaluated: one checked divisible factor suffices.

| Declaration | Checked claim |
|---|---|
| `A134559.witness_fiber` | The original remainder fiber is exactly the displayed 14-element set. |
| `A134559.witness_sum` | $b_{54217}(2737)=162651$. |
| `A134559.witness_prime_pair` | $54217>5$, and both $54217$ and $27109$ are prime. |
| `A134559.witness_divides_product` | $54217\mid P(54217)$. |
| `A134559.witness_gcd` | $\gcd(P(54217),54217)=54217$. |
| `A134559.conjecture_false` | The original characterization over positive integers is false. |

The package pins Lean **4.19.0** and mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. Reproduce with:

```sh
lake exe cache get
lake build
lake env lean Proof.lean
```

There are no admissions, additional axioms, `unsafe` declarations, or `native_decide` proofs. Printed theorem dependencies use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The small finite sum uses ordinary kernel-reduced `decide`.

`verify.py` is a separate executable sanity check using the original remainder definition. The proof does not depend on that program or its output.

## Attribution and prior-publication checks

The conjecture is Ratajczak's; the triangle was introduced by Gary W. Adamson. The checked source revision remains labeled as a conjecture and reports previous checking through 2000 integers. Both search engines and the current trureturing resolved-results index were checked for the exact identifier and related statement; no earlier resolution was located. This is a bounded search, not a certification of historical priority. See `source_checks.md` and the preserved primary-source snapshots.
