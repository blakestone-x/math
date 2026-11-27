# Exactly when the Rule 150 period equals the ring width

**Blake Stone · Proof developed with OpenAI Codex.**

On a cyclic row of $n\ge3$ bits, Rule 150 replaces each bit by the XOR of itself and its two neighbors. Start with one occupied cell. Let $P(n)$ be the eventual period of the full configuration, as tabulated in OEIS A085588. Roman Khrabrov conjectured in 2024 that $P(n)=n$ implies membership of $n$ in A115770. [A085588](https://oeis.org/A085588) · [A115770](https://oeis.org/A115770)

**Theorem.** For $n\ge3$,
$$
P(n)=n\quad\Longleftrightarrow\quad n=2^a(2^k-1)\quad\text{with }a\ge0,\ k\ge3.
$$

Thus the positive widths in question have a single run of at least three binary ones, possibly followed by zeros. We first prove a restriction on the odd part of the width, including the noninvertible case $3\mid n$.

## The period test

Write $n=e m$, where $m$ is odd and $e$ is a power of two. Represent a configuration by a polynomial in $R_n=\mathbb F_2[x]/(x^n-1)$. The variable $x$ acts as a cyclic shift and is a unit. Starting from $1$, the trajectory consists of the powers of the Laurent polynomial $F=x^{-1}+1+x$.

The polynomial $x^m-1$ has distinct roots in an algebraic closure, since $m$ is odd, and $x^n-1=(x^m-1)^e$. Write $H(x)$ for the product of the linear factors corresponding to the $m$-th roots of unity $z$ with $F(z)\ne0$. The only excluded roots are the two primitive cube roots when $3\mid m$, since $xF=1+x+x^2$. On each excluded factor modulo $(x-z)^e$, a sufficiently high power of $F$ is zero. On every other factor $F$ is a unit. The Chinese remainder theorem therefore gives, for every $h>0$,
$$
P(n)\mid h\quad\Longleftrightarrow\quad H(x)^e\mid F(x)^h-1.
\tag{1}
$$
Laurent divisibility here and below may be tested after clearing powers of $x$, which is nonzero at every root under consideration.

## Necessity: the odd part is Mersenne

Suppose $P(n)=n$. For every $m$-th root $z$ with $F(z)\ne0$, equation (1) implies $F(z)^{em}=1$. Since $e$ is a power of two, $(F(z)^m-1)^e=0$, so $F(z)^m=1$. Consider
$$
D(x)=(1+x^3)^m+(1+x)^m.
$$
In characteristic two, $1+x^3=x(1+x)F(x)$. It follows that $D(z)=0$ at every $m$-th root with $F(z)\ne0$. At an excluded primitive cube root $z$ we have $1+z=z^2$ and $3\mid m$, giving $D(z)=1$.

Let $L(x)=(1+x)^m$. In characteristic two this factors as
$$
L(x)=\prod_{i:\,\text{bit }i\text{ of }m\text{ equals }1}(1+x^{2^i}).
$$
Thus the exponents that occur in $L$ are precisely the binary submasks of $m$, the numbers obtained by deleting any choice of its set bits.

**Case $3\nmid m$.** We may assume $m>1$. Since $D$ vanishes on all the distinct $m$-th roots, $L(x^3)=L(x)$ modulo $x^m-1$. In the reduction of $L$, the constant and the degree-$m$ monomial cancel. All nonzero proper submasks occur once. Tripling is a permutation of the residues modulo $m$, so the set of these submasks is closed under tripling modulo $m$. Let $2^r\le m<2^{r+1}$. Bit zero of $m$ is one. For $0\le i\le r-2$, if bit $i$ is one, then $2^i$ is a nonzero proper submask, and $3\cdot2^i<m$. Its binary expansion has bits $i$ and $i+1$ set. Closure thus forces bit $i+1$ of $m$ to be one. This fills all bits below the leading one, so $m=2^{r+1}-1$.

**Case $3\mid m$.** Modulo $x^m-1$ the polynomial $D$ is
$$
E(x)=(x+x^2)\sum_{t=0}^{m/3-1}x^{3t}
    =\sum_{\substack{0\le j<m\\3\nmid j}}x^j.
$$
Indeed, $E$ vanishes at $1$ and at every $m$-th root whose cube differs from $1$, by the geometric sum. At either primitive cube root its value is $1$, since $m/3$ is odd. These evaluations agree with $D$ at all the distinct roots. Every exponent of $L(x^3)$ is divisible by three even after reduction modulo $x^m-1$. Consequently, at every index $j<m$ not divisible by three the coefficient of $L$ is one. In particular each power of two below $m$ is a submask, so every bit through the highest bit is present. Again $m$ is Mersenne.

## Sufficiency and exactness

Now suppose $m=2^k-1\ge7$. All $m$-th roots lie in $\mathbb F_{2^k}$, whose nonzero elements have orders dividing $m$. Hence $H\mid F^m-1$, and raising to the $e$-th power yields $H^e\mid F^n-1$. By (1), $P(n)\mid n$.

If $P(n)<n$, then $P(n)\mid n/p$ for some prime divisor $p$ of $n$. For odd $p$ we have $2n/p\le2em/3<e(m-2)$ since $m>6$. But $H^e$ has degree at least $e(m-2)$, whereas $x^{n/p}(F^{n/p}-1)$ is a nonzero polynomial of degree $2n/p$. This contradicts (1).

For $p=2$, which is a possibility only if $e\ge2$, take a primitive $m$-th root $z$. It is neither $1$ nor a primitive cube root, so $F(z)\ne0$. The derivative of $F^m-1$ is $F^{m-1}(1+x^{-2})$ in characteristic two. It does not vanish at $z$. Thus $F^m-1$ has a simple zero there, and $F^{n/2}-1=(F^m-1)^{e/2}$ has multiplicity exactly $e/2$. Equation (1) requires multiplicity at least $e$. This excludes the last possible shorter period.

For the small odd parts $m=1,3$, only the root $1$ survives. Thus $H=x-1$. The identity $F-1=x^{-1}(x-1)^2$ shows that $F^{2^j}-1$ has multiplicity exactly $2^{j+1}$ at $1$. By (1), the first power of two divisible by the period is therefore $\max(1,e/2)$. Since that power is itself a multiple of the period, the period must be a power of two and is exactly $\max(1,e/2)$. This is smaller than $n$ in both cases for $n\ge3$. ∎

The necessity argument used only $P(n)\mid n$, and every Mersenne odd part satisfies this divisibility, including $1$ and $3$. Thus $P(n)\mid n$ if and only if the odd part of $n$ is $2^k-1$ for some $k\ge1$. Among these widths the two small odd parts above are exactly the cases of strict divisibility.

## Consequences for the OEIS observations

For every width in the theorem, membership in A115770 follows from the run criterion for that sequence. It can also be checked directly. With $m=2^k-1$ and $k\ge3$, the XOR $C(11,m)=(8m)\mathbin{\oplus}(2m)\mathbin{\oplus}m$ equals $7m$: the mask $(2m)\mathbin{\oplus}m$ has just bits $0$ and $k$ set, so XOR with $8m=2^{k+3}-8$ adds $1$ and subtracts $2^k$. Shifting by $a$ places preserves the identity. Khrabrov also states that the converse fails and lists $445$ as the first exception. The first exception is actually $455=(111000111)_2$. By the [binary run criterion](../A115770/README.md), every positive member of A115770 has runs of length at least three after trailing zeros are removed. A single run gives a width in the theorem. The smallest word with two runs of ones separated by zeros is $111000111$, and $445=(110111101)_2$ fails the run criterion. [A115770](https://oeis.org/A115770) · [A085588](https://oeis.org/A085588)

A separate divisibility observation in A085588 has its direction reversed. Write $b$ for the least positive exponent with $2^b\equiv\pm1\pmod m$ when $m>1$, and put $b=1$ for $m=1$. This is A309786 evaluated at $n$: in the tent map, write an iterate as a numerator modulo $2n$, identifying the signs. Doubling the numerator eliminates the power-of-two factor, leaving the cycle of repeated doubling modulo $m$ up to sign. Then every $m$-th root satisfies $F(z)^{2^b}=1+z^{2^b}+z^{-2^b}=F(z)$, whence $H\mid F^{2^b-1}-1$. Raising to the $e$-th power in (1) proves $P(n)\mid e(2^b-1)$. At width $13$, $b=6$ and the OEIS gives $P(13)=21$, so $63$ does not divide $P(13)$. This upper-bound mechanism is classical for symmetric additive cellular automata. [A085588](https://oeis.org/A085588) · [A309786](https://oeis.org/A309786) · [Martin, Odlyzko and Wolfram, 1984](https://content.wolfram.com/sw-publications/2020/07/algebraic-properties-cellular-automata.pdf)

## Earlier work and verification

Kaneko used Frobenius squaring for the invertible Mersenne-width family and treated $7\cdot 2^a$ separately. Bojić analyzed local orders and their lifting at invertible widths. A related TrureTuring result evaluates the least common multiple of the residue-field orders for Mersenne odd parts coprime to three. These results overlap the sufficiency argument for invertible widths. The necessity proof above detects the binary structure of the odd part and also treats widths divisible by three. [Kaneko](https://arxiv.org/abs/1401.4779) · [Bojić, §§2.2–2.3 and 8](https://arxiv.org/pdf/2611.33216) · [TrureTuring local-order result](https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.html)

The accompanying check works directly with bit-packed Rule 150 states. At width $n$ the images of the linear evolution map stabilize after at most $n$ steps. From the seed advanced to that point, the checker tests period $n$ and every maximal proper divisor $n/p$. It confirms the equivalence for every $3\le n\le16384$ and cross-checks the fast method against direct orbit enumeration at widths $3$ through $33$. [Verifier](verify.py)
