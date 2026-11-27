# Infinitely many nonrepunits with prime digit sum and prime digit product plus one

Blake Stone · Proof developed with OpenAI Codex

Let $s(N)$ and $P(N)$ be the sum and product of the decimal digits of $N$. Amarnath Murthy observed that the repunit with $p$ digits qualifies for A087339 for every prime $p$. He conjectured in 2003 that infinitely many other integers qualify. [OEIS A087339](https://oeis.org/A087339)

**Theorem.** For each prime $p\ge3$, every integer consisting of one digit $2$ and $p-2$ digits $1$ has both $s(N)$ and $P(N)+1$ prime.

**Proof.** Its digit sum is $2+(p-2)=p$, and its digit product is $2$, so $P(N)+1=3$. The digit $2$ makes it a nonrepunit. Different primes give different digit lengths, and there are infinitely many primes. $\square$

For $p=5$, the four choices are $2111$, $1211$, $1121$, and $1112$. In general exactly $p-1$ integers of this form arise at length $p-1$, one for each position of the $2$.

## A general insertion rule

Fix a nonempty word $w$ of $r$ digits from $\{2,\ldots,9\}$. Write $S$ and $P$ for its digit sum and product. Insert $t\ge0$ copies of the digit $1$, keeping the digits of $w$ in their original order. Every resulting integer has digit product $P$ and digit sum $S+t$. Thus the whole family at that length qualifies exactly when $P+1$ and $S+t$ are both prime.

In particular, if $P+1$ is prime, each prime $p\ge S$ yields exactly $\binom{p-S+r}{r}$ qualifying integers that reduce to $w$ upon deletion of all ones. Indeed, choose the $r$ positions occupied by $w$ out of the $p-S+r$ total positions. This counts distinct integers even when $w$ has repeated digits, because the positions of its digits can be recovered by deleting the ones. If $P+1$ is composite, no insertion works. The single-digit word $w=2$ gives the theorem.
