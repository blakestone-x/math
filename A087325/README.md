# The least 10's-complement pair with a prescribed number of prime factors

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

For a positive integer $x$ with $d$ decimal digits, put $y=10^d-x$. An integer $x$ belongs to A087325 if $x$ and $y$ have the same **prime signature**, the multiset of exponents in their prime factorizations. Write $\Omega(x)$ for the sum of those exponents, so factors are counted with multiplicity. In July 2024 Robert Israel gave an empirical formula for the first term with $\Omega(x)=m$. [OEIS A087325](https://oeis.org/A087325)

**Theorem.** Let $L_m$ be the smallest qualifying $x$ with $\Omega(x)=m$. For every integer $m\ge1$,

$$
L_m =
\begin{cases}
3\cdot10^{(m-1)/2} & m\text{ odd},\\
14 & m=2,\\
132\cdot10^{(m-4)/2} & m\ge4\text{ even}.
\end{cases}
$$

## Dividing both members by ten

Write $v_p(z)$ for the exponent of the prime $p$ in $z$, using zero when $p$ does not divide $z$. In every qualifying pair,

$$
v_2(x)=v_2(y)<d,\qquad v_5(x)=v_5(y)\le d.
$$

To prove equality, take $p=2$ or $5$. If its two valuations differ, their minimum must be $v_p(x+y)=d$. Its other valuation is some $e>d$. The common signature therefore contains both $d$ and $e$. In each number there must then be a second prime, distinct from $p$, with exponent at least $d$. For $p=5$, each number would be at least $5^d2^d=10^d$, which is impossible. For $p=2$, any such second prime at least $5$ would give the same contradiction. Thus the second prime must be $3$ on both sides. This would make $x+y=10^d$ divisible by $3$. Both contradictions prove equality. The common valuations are at most $d$ since $x+y=10^d$. If the common $2$-valuation were exactly $d$, dividing the sum by $2^d$ would express the odd number $5^d$ as a sum of two odd numbers.

Consequently appending a zero to both members preserves signature equality. It increases the same two valuations on each side and leaves the other exponents alone. Conversely, whenever $10\mid x$, both numbers can be divided by ten. The resulting pair has equal signatures, is still a complement pair for the shorter decimal length of $x/10$, and has two fewer prime factors per member. Israel had already observed the forward closure under multiplication by ten. [OEIS A087325](https://oeis.org/A087325)

The pairs $(3,7)$, $(14,86)$ and $(132,868)$ qualify. In particular $132=2^2\cdot3\cdot11$ and $868=2^2\cdot7\cdot31$. They and their multiples by powers of ten supply all the upper bounds in the theorem.

## Why sufficiently large minima have a trailing zero

Suppose $10\nmid x$. At least one member of the pair is free of the prime $3$, since $3\nmid10^d$. Both members have exactly $m$ prime factors counted with multiplicity.

- If $x$ is odd, both numbers are odd. Every prime in the member free of $3$ is at least $5$, so this member is at least $5^m$.
- If $x$ is even, both numbers are even and neither is divisible by $5$. Put $a=v_2(x)=v_2(y)<d$. In the member free of $3$, all $m-a$ prime factors other than $2$ are at least $7$. This member is at least $2^a7^{m-a}$.

**Odd case.** Write $m=2s+1$ and suppose $s\ge2$. Any contender $x\le3\cdot10^s$ has $d\le s+1$. Each member must be less than $10^d\le10^{s+1}$. The odd-member bound $5^{2s+1}$ already exceeds $10^{s+1}$. In the even case, $a\le s$, so the lower bound is at least $2^s7^{s+1}=7\cdot14^s>10^{s+1}$. Both inequalities hold at $s=2$ and their ratios to $10^{s+1}$ increase with $s$.

**Even case.** Write $m=2s$ and suppose $s\ge7$. Any contender $x\le132\cdot10^{s-2}$ again has $d\le s+1$. The odd-member bound $5^{2s}$ exceeds $10^{s+1}$. In the even case, $a\le s$ gives the lower bound $2^s7^s=14^s>10^{s+1}$. Indeed, $14^7=105413504>10^8$, and the ratio increases by a factor of $1.4$ at each step.

Thus every contender in these ranges must be divisible by ten. Dividing a minimizer by ten gives $L_m\ge10L_{m-2}$, and multiplying a minimizer for $m-2$ by ten gives the reverse inequality. Hence $L_m=10L_{m-2}$ throughout both ranges.

## Finite base cases

For $m=1,\ldots,12$, exhaustive factorization gives

| $m$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $L_m$ | 3 | 14 | 30 | 132 | 300 | 1320 | 3000 | 13200 | 30000 | 132000 | 300000 | 1320000 |

The [finite verifier](verify.py) scans every $x$ from $1$ through $1{,}320{,}000$ in increasing order. A smallest-prime-factor sieve covers $x$ and every possible complement up to $9{,}999{,}999$. The program sorts the exponents in each factorization and records the first equality for each required $m$. The table and the recurrence prove the stated minima for every $m$. $\square$
