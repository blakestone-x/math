# A sharp power bound for the next integer with a given prime signature

**Blake Stone · Proof developed with OpenAI Codex.**

In a comment on A083788, Amarnath Murthy asked how far above an integer $n$ one must look to find another integer of the same prime signature. The signature is the multiset of positive exponents in the prime factorization. The entry asks for a tight upper endpoint without specifying its form. We determine the optimal **universal power bound**, and give a factorization-dependent witness as well. [OEIS A083788](https://oeis.org/A083788)

**Theorem.** For $n\ge2$, let $S(n)$ be the least integer greater than $n$ of the same prime signature. Then

$$
S(n)\le n^{\log_2 3}.
$$

Equality holds precisely at the powers of two. Thus $\log_2 3$ is the smallest exponent that works for every $n\ge2$, even if the inequality is required only for all sufficiently large $n$. In the strict-endpoint convention $n<k<m$ used in the OEIS question, one may take $m=\lfloor n^{\log_2 3}\rfloor+1$. The case $n=1$ has no successor, since only $1$ has the empty signature.

**Proof.** Write $n=uP^a$ with $P$ its largest prime divisor and $P\nmid u$. Let $Q$ be the next prime after $P$. Then $uQ^a>n$ has exactly the same signature as $n$, so

$$
S(n)\le uQ^a=n(Q/P)^a.
$$

Put $c=\log_2 3$. Since $3^2>2^3$, we have $c>3/2$. If $P\ge5$, Bertrand's postulate gives $Q<2P<P^{3/2}$. For $P=3$, one has $Q=5<3^{3/2}$. Thus for every $P\ge3$,

$$
S(n)\le uQ^a<uP^{ac}\le (uP^a)^c=n^c.
$$

If $P=2$, then $n=2^a$. Every integer with the one-exponent signature $(a)$ is a prime raised to the $a$th power, so its successor is exactly $3^a=(2^a)^c$. These inputs give equality for unbounded $n$. $\square$ [Bertrand's postulate and its elementary proof](https://math.stanford.edu/~ksound/Math155W10/Bertrand.pdf)

**Bounds using the factorization.** For any $p\mid n$, replace $p$ with the smallest larger prime $q_p$ that does not divide $n$. This gives the explicit integer bound

$$
S(n)\le \min_{p\mid n} n\,(q_p/p)^{v_p(n)}.
$$

For example, $12=2^2\cdot3$. Replacing $3$ with $5$ gives $20$, whereas replacing $2$ with $5$ gives $75$. Either replacement preserves the signature.

More generally, restrict attention to integers whose largest prime divisor is at least $T\ge2$. The sharp universal exponent for that class is

$$
c_T=\max_{\substack{p\ \mathrm{prime}\\p\ge T}}
                 \frac{\log p^+}{\log p},
$$

where $p^+$ is the next prime. This maximum is attained: Bertrand gives $\log p^+/\log p<1+\log 2/\log p$, which tends to $1$, and each eligible prime gives a ratio strictly above $1$. For any such $n$, the replacement of its largest prime gives $S(n)\le n^{c_T}$. Powers of any maximizing prime attain equality, proving sharpness.
