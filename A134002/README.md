# An exact count for Layman’s conjecture, OEIS A134002

For every positive integer $n$, the number of **ordered** pairs of positive integers $(a,b)$ satisfying
$$
 n(n+5)=a(a+5)+b(b+5)
$$
is exactly $\tau(n^2+(n+5)^2)-2$, where $\tau$ counts positive divisors. Consequently, the equation is solvable precisely when $n^2+(n+5)^2$ is composite. This proves the implication conjectured by John W. Layman in 2007. The entry specifies positive $n$ and positive unknowns. [OEIS A134002](https://oeis.org/A134002)

**Proof.** Write $M=n^2+(n+5)^2$. The two summands have opposite parity, so $M$ is odd. If a prime $p\equiv3\pmod4$ divides $M$, the fact that $-1$ is a quadratic nonresidue modulo $p$ forces $p\mid n$ and $p\mid n+5$. This implies $p\mid5$, a contradiction. Therefore all divisors of $M$ are $1\pmod4$.

Jacobi’s two-square theorem gives $r_2(t)=4(d_1(t)-d_3(t))$, where $r_2$ counts signed, ordered representations and $d_i$ counts positive divisors congruent to $i\pmod4$. The odd divisors of $2M$ are precisely the divisors of $M$. Consequently $r_2(2M)=4\tau(M)$. Since $2M\equiv2\pmod4$, both coordinates are odd and nonzero. Dividing out their four independent sign choices leaves exactly $\tau(M)$ ordered positive pairs $(x,y)$ with $x^2+y^2=2M$. [M. D. Hirschhorn, *Arithmetic Consequences of Jacobi’s Two-Squares Theorem*, Theorem 1](https://web.maths.unsw.edu.au/~mikeh/webpapers/paper68.pdf)

Put $s=2n+5\ge7$, so $2M=s^2+25$. If a positive coordinate were $c=1$ or $3$, the other odd coordinate would have square $s^2+25-c^2$. This lies strictly between the consecutive odd squares $s^2$ and $(s+2)^2$, since $0<25-c^2\le24<4s+4$. A coordinate equal to five gives exactly the ordered pairs $(5,s)$ and $(s,5)$. The remaining $\tau(M)-2$ pairs all have coordinates at least seven. Set $a=(x-5)/2$ and $b=(y-5)/2$. Completing squares gives a bijection with the ordered positive solutions of the original equation. Since $M>1$, the number of solutions vanishes exactly when $M$ is prime. ∎

At the entry’s first term, $n=5$ and $M=125$. Its four divisors predict two ordered solutions, $(2,4)$ and $(4,2)$. The positivity condition on $n$ matters: at $n=0$ the equation has no positive solutions although $M=25$.

## Lean verification

The accompanying Lean theorem proves Layman’s implication by a constructive route. A composite value factors as two integers greater than one. Each factor has a positive sum-of-two-squares representation with unequal coordinates, by Fermat’s theorem and induction on the prime factors. Write the two pairs as $(x,y)$ and $(s,t)$, with $0<x<y$ and $0<s<t$. The product identity gives the representations
$$
 (yt-xs,\,xt+ys),\qquad (|xt-ys|,\,xs+yt).
$$
The largest coordinate of the second pair exceeds both coordinates of the first, since $(y-x)(t-s)>0$. At least one of these representations differs, up to ordering, from $(n,n+5)$. Its sum and difference give a representation of $2M$ with both coordinates at least seven, by the same gap-between-odd-squares argument above. The formal theorem uses this construction to establish the existence required by the OEIS conjecture. The exact divisor-count identity above uses Jacobi’s theorem in the written proof.

[Lean statement](statements/oeis-a134002.lean) · [Complete Lean proof](proofs/oeis-a134002.lean) · [Local kernel verdict](proof-verdict.json) · [Board submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18282)
