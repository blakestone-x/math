# A300984: squarefree sums of squarefree and nonsquarefree divisors

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Statement and result

For a positive integer $n$, define the two sums over its positive divisors by

$$S(n)=\sum_{\substack{d\mid n\\d\text{ squarefree}}}d,
\qquad T(n)=\sum_{\substack{d\mid n\\d\text{ not squarefree}}}d.$$

[OEIS A300984](https://oeis.org/A300984), created by Michel Lagneau on March 17, 2018, consists of the integers for which **both** $S(n)$ and $T(n)$ are squarefree. Its recorded conjecture says that every member has the form $2^i p^j$, with $p$ prime.

We prove the conjecture for every positive integer and obtain the stronger necessary conditions

$$\boxed{n=2^i p^j,\qquad i,j\ge2,\qquad p\text{ prime},\qquad
p\equiv1\pmod{12},\qquad 3(p+1)\text{ squarefree}.}$$

These conditions imply $n\ge676$. They are necessary conditions, not a converse characterization: squarefreeness of $T(n)$ still imposes further restrictions. The separate OEIS conjecture about a majority of the relevant primes belonging to A082539 is outside this result.

The result uses a known product formula and a prior squarefree-divisor obstruction. The exact relationship to that prior work is explained below.

## Proof

### 1. The squarefree-divisor product

Let $P(n)$ be the finite set of distinct prime divisors of $n$. Every squarefree divisor corresponds to exactly one subset of $P(n)$, namely the primes occurring in that divisor. Expanding a product therefore gives

$$S(n)=\prod_{q\in P(n)}(1+q). \tag{1}$$

This identity is classical; [A048250](https://oeis.org/A048250) records the product formula under Vladeta Jovovic's April 19, 2001 contribution. Equivalently, $S(n)=\sigma(\operatorname{rad}(n))$.

Suppose two distinct odd primes $p,q$ divide $n$. Both $p+1$ and $q+1$ are even. Equation (1) shows that $(p+1)(q+1)$ divides $S(n)$, so $4\mid S(n)$, contrary to squarefreeness. Thus at most one odd prime divides $n$.

Unique factorization already gives $n=2^i p^j$, allowing zero exponents at this stage. If there is no odd prime divisor, one can take any fixed odd prime with exponent zero. This proves the recorded shape conjecture using the first sum alone.

### 2. The second sum forces two distinct prime squares

We prove a useful general observation:

> If $T(n)$ is squarefree, then two distinct prime squares divide $n$.

If no prime square divides $n$, then $n$ is squarefree. Every divisor of $n$ is then squarefree, so $T(n)=0$. This is impossible because zero is not squarefree.

Now suppose exactly one prime square, say $r^2$, divides $n$. Every nonsquarefree divisor $d$ of $n$ is divisible by some prime square $s^2$. Since $s^2\mid d\mid n$, uniqueness forces $s=r$. Hence **every summand** of $T(n)$ is divisible by $r^2$, so their sum is divisible by $r^2$. That again contradicts squarefreeness.

Consequently at least two distinct prime squares divide $n$. From the first part there is at most one odd prime divisor. The two primes must therefore be $2$ and an odd prime $p$, and both $4$ and $p^2$ divide $n$. Thus the exponents in $n=2^i p^j$ satisfy $i,j\ge2$.

### 3. The congruence condition on the odd prime

The distinct prime divisors are now exactly $2,p$, so (1) becomes

$$S(n)=3(p+1).$$

Because this is squarefree, $4$ cannot divide $p+1$. The prime $p$ is odd, so this gives $p\equiv1\pmod4$.

Also, $3$ cannot divide $p+1$, or else $9$ would divide $3(p+1)$. We cannot have $p=3$, since that would make $p+1=4$. Since $p$ is a prime different from $3$, its only remaining residue modulo $3$ is $1$. Combining the two congruences yields

$$p\equiv1\pmod{12}.$$

This completes the strengthened theorem. In particular, $p\ge13$, so

$$n=2^i p^j\ge 2^2\,13^2=676.$$

The displayed first term is consistent with this bound: at $676=4\cdot13^2$ the squarefree divisors are $1,2,13,26$, giving $S(676)=42=2\cdot3\cdot7$. The other divisors are $4,52,169,338,676$, giving $T(676)=1239=3\cdot7\cdot59$. Both sums are squarefree. The formal file proves the universal lower bound; this final numerical illustration is an elementary calculation.

## Prior work and contribution scope

Walter Kehowski's March 21, 2007 comment on [A065302](https://oeis.org/A065302) proves that a squarefree nonprime integer whose ordinary divisor sum is squarefree is either $1$ or $2p$, with $p\equiv1\pmod{12}$. His proof explicitly uses the divisibility of $(p+1)(q+1)$ by $4$ for odd primes.

That result is stated for squarefree integers and the ordinary divisor sum. Applying the same obstruction to the radical of an arbitrary $n$ supplies the prime-support restriction here. We credit that argument and its congruence consequence to Kehowski, rather than presenting them as a new multiplicative theory. The second divisor sum forces the extra exponent restrictions $i,j\ge2$.

The contribution of this package is an explicit proof of A300984's recorded general-$n$ conjecture, its strengthened necessary conditions, and a complete formal verification beginning with the original two divisor sums. The current official export still labels the shape assertion a conjecture. The bounded literature and proof-collection searches described in [source_checks.md](source_checks.md) did not locate an earlier proof of this exact two-sum statement; they do not establish absolute priority.

## Formal verification

`Proof.lean` uses `Nat.divisors` and the standard predicate `Squarefree` directly. It does not replace the original definition by the desired factorization, introduce a finite cutoff, or assume a factorization theorem as a hypothesis of the final result.

| Declaration | Meaning |
|---|---|
| `A300984.squarefreeSum`, `A300984.nonsquarefreeSum` | The two original finite divisor sums |
| `A300984.Member` | A positive integer with both sums squarefree |
| `A300984.squarefreeSum_eq_prod` | Equation (1), proved from the divisor-sum definition |
| `A300984.conjecture` | Every member is $2^i p^j$ for a prime $p$ |
| `A300984.two_squared_prime_divisors` | Squarefree $T(n)$ forces two distinct squared prime divisors |
| `A300984.strengthened_conjecture` | The complete boxed necessary conditions above |
| `A300984.member_ge_676` | Every member is at least $676$ |

The package pins **Lean 4.19.0** and Mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. In this directory, with Lean installed, run:

```sh
lake update
lake exe cache get
lake build
```

For an already provisioned checkout, `lake build` suffices. `verification.txt` records the successful packaged build. The five reported theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; the source contains no `sorry`, new axiom declarations, `native_decide`, or external proof oracle. The independent audit is recorded separately in `AUDIT.md` and `audit-verification.txt`.

## A correction to the finite prime count

The prime $937$ also occurs below $10^7$. At $n=4\cdot937^2=3{,}511{,}876$ the two divisor sums are $2814=2\cdot3\cdot7\cdot67$ and $6{,}149{,}535=3\cdot5\cdot7\cdot58{,}567$. The smaller prime 13 excludes 937 from A082539 because $14\mid938$. This corrects Lagneau's finite example to 39 of 47 prime bases, or 82.98%. The strict majority persists through $10^{16}$, where the count is 369,981 of 644,008. The conjecture at all decimal cutoffs remains open. [Proof and table](prime-counts.pdf) · [LaTeX](prime-counts.tex) · [Machine-readable counts](majority.csv)

From this directory run the following to reproduce the complete table and the independent audit through $10^9$. The audit enumerates the original divisors and requires SymPy. [Sieve](majority.cpp) · [Divisor audit](check_majority.py)

```sh
c++ -O3 -std=c++17 majority.cpp -o /tmp/a300984-majority
/tmp/a300984-majority 16
python3 -B check_majority.py
```

## The geometric-sum step on Left to Solve

For every odd prime $p$, $j>0$ and $i\ge0$, Lean now proves both divisor-sum formulas from their original definitions. The squarefree sum is $(1+p)$ for $i=0$ and $3(1+p)$ for $i>0$. The sum over the other divisors is the product of the two geometric series minus that squarefree sum. This supplies H1 of the reduction proposed by @dwilfand-sys. Its H2 is the open majority assertion. [Lean theorem](DivisorFormulas.lean) · [Proposed reduction, PR 16565](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16565) · [Prepared proof of H1](https://github.com/blakestone-x/open-math-agents/blob/7f0b2c15ade39d044ecbb9dd53f5ff0af5fdb87e/proofs/oeis-a300984.R1.H1.lean)

Lean 4.33.1 checked the standalone theorem and the adapter to the proposed H1 with the standard three axioms. For the adapter check the statement imported the relevant Mathlib modules individually. Its definitions and the proposed reduction were copied verbatim. The board can accept a step submission after the parent reduction merges.
