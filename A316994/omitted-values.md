# If A316994 omits one integer, its range has density zero

**Blake Stone · Proof developed with OpenAI Codex.**

Rémy Sigrist's binary sequence starts at $a_1=2$. Given the partial sum $S_n=a_1+\cdots+a_n$, choose the least unused positive integer $x$ whose ordinary binary expansion is a substring of $S_n+x$ in binary. The rule always has a next term. Once $n\ge2$, $S_n$ itself is unused and its binary expansion is a prefix of $2S_n$. The permutation conjecture in the original entry remains unresolved here. [OEIS A316994](https://oeis.org/A316994)

**Theorem.** Suppose a positive integer $k$ never occurs. Let $d$ be its binary length and put

$$
\alpha=\frac{\log_2(2^{2d}-1)}{2d}<1.
$$

If $R(X)$ counts the distinct values in the entire sequence that are at most $X$, then $R(X)=O_k(X^\alpha)$. In particular, positive upper density of the range would imply that the sequence is a permutation.

**Proof.** Write $w$ for the binary expansion of $k$. There are at most $k-1$ indices $n$ for which $S_n+k$ contains $w$. At each such index, $k$ would be eligible for the next step. Because it is never selected, the greedy rule must choose a previously unused positive integer smaller than $k$. There are only $k-1$ such choices.

Now form the word $W$ by appending $d$ zeros to $w$. Whenever $W$ occurs in $a_n$, it also occurs in $S_n$, by the defining substring condition. Suppose there are $q$ bits to the right of that occurrence in $S_n$. The $q+d$ lowest bits of $S_n$ consist of $d$ zeros followed by those $q$ bits, so their value $v$ is less than $2^q$. Since $k<2^d$,

$$
v+k\le (2^q-1)+(2^d-1)<2^{q+d}.
$$

Thus adding $k$ leaves unchanged every bit at or above position $q+d$, with bit positions counted from zero. The displayed copy of $w$ is among those unchanged bits. It follows that every term containing $W$ gives one of the at most $k-1$ indices just identified.

Set $h=2d$. Among binary words of length $L$, at most

$$
(2^h-1)^{\lfloor L/h\rfloor}\,2^{L\bmod h}
$$

avoid $W$. In each disjoint block of $h$ bits the particular word $W$ is forbidden, and the final incomplete block contributes at most $2^{h-1}$ choices. This bounds the count by $O_k(2^{\alpha L})$. Summing over $L\le\lfloor\log_2 X\rfloor+1$ and adding the at most $k-1$ exceptional terms proves the theorem. $\square$

**Consequence for growth.** Under the same omission hypothesis, $S_n\gg_k n^{1+1/\alpha}$. Indeed, choose $C$ with $R(X)\le C X^\alpha$ for $X\ge1$. Of the first $n$ distinct terms, at least half exceed $(n/(2C))^{1/\alpha}$ for all sufficiently large $n$. The exponent $1+1/\alpha$ exceeds $2$, so an upper bound $S_n\le n^{2+o(1)}$ would also prove the permutation conjecture.
