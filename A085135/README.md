# Smooth numbers and a single cyclic digit rotation

Blake Stone · Proof developed with OpenAI Codex

An integer is **7-smooth** if every prime dividing it is one of $2,3,5,7$. In 2003 Amarnath Murthy and Meenakshi Srikanth conjectured that only finitely many decimal integers with at least two nonzero digits have all their cyclic digit rotations 7-smooth. Their examples include $243,432,324$, whose largest prime factor is $3$. [OEIS A085135](https://oeis.org/A085135)

**Theorem.** Fix a base $b\ge2$ and a finite set $S$ of primes. There are only finitely many positive integers $N$ with at least two nonzero base-$b$ digits such that both $N$ and the integer obtained by moving its first digit to the end have all their prime factors in $S$. A rotation that begins with zeros is evaluated at its usual integer value.

In particular, even requiring just this one rotation as well as $N$ to be 7-smooth proves the A085135 finiteness conjecture. The exceptional decimal numbers with a single nonzero digit have the form $a10^j$ for $1\le a\le9$. Every fixed-width rotation of one of these numbers is again of this form and hence 7-smooth.

## Proof

Fix the leading digit $a$, where $1\le a<b$. Write $N=ab^{d-1}+u$ with $d$ the number of digits. The one-step rotation is $R=bu+a$. Therefore

$$
\frac{R}{a}+b^d-\frac{bN}{a}=1.
$$

Let $T$ consist of $S$ together with the primes dividing $ab$. The positive rational numbers whose numerators and denominators have all their prime factors in $T$ form the finitely generated multiplicative group $G=\langle p:p\in T\rangle$. All three quantities $R/a,b^d,bN/a$ lie in $G$.

We apply the characteristic-zero unit-equation theorem of Evertse, Schlickewei and Schmidt. For a finite-rank multiplicative group such as $G^3$, the equation $X+Y-Z=1$ has finitely many solutions for which no nonempty subsum on the left vanishes. [Evertse, Schlickewei and Schmidt, Theorem 1.1, *Annals of Mathematics* 155 (2002), 807–836](https://doi.org/10.2307/3062133)

Here each individual term is nonzero, the two positive terms have positive sum, and the whole left side is one. This leaves only two possible cancellations. The equality $R=bN$ is impossible because $bN-R=a(b^d-1)>0$. The equality $b^d=bN/a$ occurs precisely when $N=ab^{d-1}$, or equivalently $u=0$. A second nonzero digit rules this out. Thus every integer under consideration gives a nondegenerate solution of the unit equation.

For fixed $a$ the third coordinate $bN/a$ uniquely determines $N$. Finiteness of the solutions therefore gives finiteness of $N$. There are only $b-1$ choices for $a$. $\square$

The conclusion is finiteness. Determining the complete list of decimal exceptions would require an additional argument.

A [companion manuscript](../Smooth-gaps/smooth-rotations.pdf) classifies the 33 nontrivial terms with exactly two nonzero digits, with a cyclic gap of at most three positions between successive nonzero digits, or with at least one quarter of all digits nonzero. It also proves that every positive 7-smooth decimal integer has full period.
