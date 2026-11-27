# The greedy binary-substring sequence A316994 is infinite

**Blake Stone · Proof developed with OpenAI Codex.**

Rémy Sigrist's sequence starts with $a_1=2$. Write $S_n=a_1+\cdots+a_n$. The next term is the least unused positive integer $x$ whose ordinary binary expansion occurs as a contiguous substring of the binary expansion of $S_n+x$. Sigrist conjectured in 2018 that the sequence is infinite, and separately that it is a permutation of the positive integers. [OEIS A316994](https://oeis.org/A316994)

**Theorem.** At every stage the greedy rule has a legal next term. For $n\ge2$, it satisfies $a_{n+1}\le S_n$.

**Proof.** The second term is $1$, since the binary expansion of $2+1$ is $11$. Suppose $n\ge2$ terms have been chosen. Their sum $S_n$ strictly exceeds each one, so $S_n$ is unused. Choose $x=S_n$ as a candidate. The new sum would be $2S_n$, whose binary expansion is the expansion of $S_n$ followed by one zero. Thus the required substring occurs as a prefix. The greedy rule can choose its least legal candidate, which is at most $S_n$. Induction gives infinitely many terms. $\square$

Whether every positive integer eventually occurs remains open. The [density theorem](omitted-values.md) proves that omitting even one value would force the range of the sequence to have density zero.
