# Every integer has a nontrivial multiple with the same product of nonzero digits

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

Let $P(n)$ be the product of the **nonzero** decimal digits of $n$. In 2003 Amarnath Murthy asked whether every positive integer $n$ has a multiple $M$ with $P(M)=P(n)$ other than $n$ and its decimal shifts $10^k n$. The sequence records the smallest such multiple, or zero if none exists. [OEIS A087304](https://oeis.org/A087304)

**Theorem.** Every $n\ge1$ has infinitely many such multiples. In particular, A087304 has no zero term.

## Proof

First choose a positive multiple $Q$ of $n$ whose digits belong to $\{0,1\}$. Here is the classical pigeonhole argument. Let $R_i$ be the number with $i$ consecutive ones, with $R_0=0$. Two of $R_0,\ldots,R_n$ have the same residue modulo $n$. If their indices are $i<j$, then $Q=R_j-R_i=10^iR_{j-i}$ is positive, divisible by $n$, and consists of ones followed by zeros. [Stanford CS103, The Pigeonhole Principle](https://web.stanford.edu/class/archive/cs/cs103/cs103.1152/lectures/10/Small10.pdf)

For every integer $L$ at least the decimal length of $Q$, put

$$
M_L=n\,10^L+Q.
$$

The two summands have disjoint digit positions. The decimal expansion starts with $n$ and appends only zeros and ones. Therefore $P(M_L)=P(n)$. Also $n\mid M_L$ and

$$
n\,10^L<M_L<(n+1)10^L\le n\,10^{L+1}.
$$

Thus $M_L$ falls strictly between consecutive decimal shifts of $n$. The values increase strictly with $L$, proving infinitude.

For example, $Q=111=3\cdot37$ gives $M_3=37{,}111=1003\cdot37$. Both $37$ and $37{,}111$ have nonzero-digit product $21$.

The same proof works in every integer base $b\ge2$, replacing powers of ten by powers of $b$. The construction establishes existence independently of the search for the least witness.
