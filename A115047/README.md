# The optimal divisibility multiplier for A115047

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Michael Somos proposed in 2014 that a prime index divides the corresponding term of A115047. Its first term is $v_3=1$.

**Theorem.** For every $n\ge 3$, $n\mid 12v_n$. The positive integers $C$ for which $n\mid Cv_n$ at every index are exactly the multiples of 12. In particular $p\mid v_p$ for every prime $p\ge 5$, and 3 is the sole prime exception in the domain.

**Proof.** For $n\ge 4$, Zograf's recurrence, reindexed by $j=i+1$, is

$$
2(n-1)v_n=\sum_{j=2}^{n-2}\binom{n-4}{j-2}\binom{n}{j}
 (j-1)(n-j-1)v_{j+1}v_{n-j+1}.
$$

The terms are integers by the border-strip enumeration of Alexandersson and Jordan. Put $D_n=(n-1)(n-2)(n-3)$. Expanding the factorials gives

$$
D_n\binom{n-4}{j-2}\binom{n}{j}
=n(j-1)(n-j-1)\binom{n-1}{j-1}\binom{n-1}{j}.
$$

Multiplying the recurrence by $D_n$ therefore makes each summand a multiple of $n$. The left multiplier satisfies $2(n-1)D_n=2(n-1)^2(n-2)(n-3)\equiv 12\pmod n$, which proves $n\mid 12v_n$. This also holds at $n=3$. The first two terms are $v_3=v_4=1$, so any universal multiplier must be divisible by 3 and 4. This proves optimality. At every prime $p\ge5$ we have $\gcd(p,12)=1$. ∎

**References.** Michael Somos's question appears in [OEIS A115047](https://oeis.org/A115047). For Zograf's recurrence and integrality see P. Alexandersson and L. Jordan, [Enumeration of Border-Strip Decompositions and Weil-Petersson Volumes](https://cs.uwaterloo.ca/journals/JIS/VOL22/Alexandersson/alex4.pdf), Theorems 32 and 34.

[Collected proof PDF, page 1](../notes/compositions-and-divisibility/OEIS-Compositions-and-Divisibility.pdf) · [Source and exact checks](../notes/compositions-and-divisibility/)
