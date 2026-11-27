# Counting divisor triples of bounded sum

Blake Stone · Proof developed with OpenAI Codex

Jonathan A. Cohen's A093035 counts ordered triples of positive divisors of $n$ whose sum is at most $n$. Michel Marcus asked for a formula in 2013. David A. Corneth subsequently gave the odd-input argument in A335018 and discussed the variation within a prime signature. The following formula covers every positive integer. [A093035](https://oeis.org/A093035) · [A335018](https://oeis.org/A335018)

**Theorem.** Let $t=\tau(n)$ be the number of positive divisors of $n$, and write $[m\mid n]$ for the indicator of divisibility. Then

$$
A093035(n)=(t-1)^3-(3t-5)[2\mid n]-3[6\mid n]-6[12\mid n]-6[30\mid n].
$$

## Proof

A triple containing $n$ cannot be counted. There are $(t-1)^3$ ordered triples of proper divisors, including triples with repetitions. To remove the triples whose sum exceeds $n$, write their entries, ignoring order for now, as $n/i,n/j,n/k$ with $2\le i\le j\le k$ dividing $n$. The forbidden condition is

$$
\frac1i+\frac1j+\frac1k>1.
$$

This forces $i=2$, since otherwise all three reciprocals are at most $1/3$. Also $j\le3$, since $1/2+1/4+1/4=1$. If $j=2$, any allowed denominator $k$ works. If $j=3$, the inequality is equivalent to $k<6$. This yields all the corrections:

| Sorted denominators | Condition | Ordered triples to remove |
|---|---|---:|
| $(2,2,k)$ for $k\ge2$ | $2\mid n$ | $1+3(t-2)=3t-5$ |
| $(2,3,3)$ | $6\mid n$ | $3$ |
| $(2,3,4)$ | $12\mid n$ | $6$ |
| $(2,3,5)$ | $30\mid n$ | $6$ |

In the first row $k=2$ gives one ordering. Each of the other $t-2$ divisors $k>2$ gives three. The rows are disjoint, and subtracting them proves the formula. $\square$

## Variation within a prime signature

The value of $t$ is fixed by a prime signature, since $t=\prod_j(e_j+1)$ for prime exponents $e_j$. All odd representatives attain the maximum $(t-1)^3$, as follows from Corneth's odd case. The least odd representative, recorded in A233819, therefore attains the maximum in every signature. [A233819](https://oeis.org/A233819) · [A335018](https://oeis.org/A335018)

The complete formula shows that a signature gives at most **five** different values. An even input first subtracts $3t-5$. If $3\nmid n$, the additional correction is zero. If $3\mid n$, the additional correction is $3$, $9$, or $15$, depending on whether zero, one, or both of $4$ and $5$ divide $n$.

The bound is attained already for signature $(2,1,1)$, where $t=12$:

| $n$ | 315 | 140 | 126 | 84 | 60 |
|---|---:|---:|---:|---:|---:|
| $A093035(n)$ | 1331 | 1300 | 1297 | 1291 | 1285 |

In particular, even integers of the same signature can give different counts. For the smallest example of this phenomenon, $6$ and $10$ have signature $(1,1)$ and counts $17$ and $20$.
