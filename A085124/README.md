# When an integer divides both a number and its digit product

Blake Stone · Proof developed with OpenAI Astra 6.2

In 2003, Amarnath Murthy asked which positive integers $n$ divide both a positive decimal integer $N$ and the **positive** product of its digits. OEIS A085124 gives the smallest such $N$, or zero if none exists. We prove the conjectured classification and give its analogue in every base. [OEIS A085124](https://oeis.org/A085124)

**Theorem.** Fix an integer base $b\ge 2$. Write $P_b(N)$ for the product of the digits of the usual base-$b$ expansion of $N$. There is a positive integer $N$ satisfying

$$
n\mid N,\qquad P_b(N)>0,\qquad n\mid P_b(N)
$$

if and only if $b\nmid n$ and every prime factor of $n$ is less than $b$. Whenever a witness exists, infinitely many witnesses exist. In decimal, the permitted prime factors are $2,3,5,7$, and the excluded multiples of $10$ are exactly the integers containing both $2$ and $5$ as factors.

## Proof

**Necessity.** Each digit contributing to a positive digit product lies between $1$ and $b-1$, so its prime factors are all less than $b$. If $b\mid n$, every multiple of $n$ ends in a zero digit.

**Sufficiency.** Assume the two stated conditions. Write $n=hm$, where $h$ contains the full prime powers of $n$ whose primes divide $b$. Thus $\gcd(m,b)=1$ and $\gcd(h,m)=1$. We first build a suffix that takes care of $h$, then repeat a block to take care of $m$.

Choose $J\ge0$ with $h\mid b^J$ and put $g_j=\gcd(n,b^j)$, so $g_0=1$ and $g_J=h$. Start with the empty suffix $v_0=0$. Suppose we have chosen $j$ nonzero digits with value $v_j$ divisible by $g_j$. To prepend one more digit $d$, set $v_{j+1}=v_j+d b^j$. The condition $g_{j+1}\mid v_{j+1}$ is equivalent to

$$
\frac{v_j}{g_j}+d\,\frac{b^j}{g_j}\equiv0\pmod{q_j},
\qquad q_j=\frac{g_{j+1}}{g_j}.
$$

Since $b^j/g_j$ and $n/g_j$ are coprime, $q_j=\gcd(n/g_j,b)$ and the coefficient of $d$ is coprime to $q_j$. Moreover $q_j\mid\gcd(n,b)<b$. We may therefore choose $d$ from $1,\ldots,q_j$, a complete residue system consisting of allowed digits. When $q_j=1$, choose $d=1$. This constructs the desired suffix $v_J$.

Form a prefix by writing the prime factors of $n$, with multiplicity, as single base-$b$ digits. Use the digit $1$ when $n=1$. Append the suffix $v_J$ to form a block with value $U$ and length $L$. Its digit product is positive and divisible by $n$. Also $h\mid U$ because $h$ divides both $b^J$ and $v_J$. For $J=0$ the block consists of the prefix alone.

Set $B=b^L$. For $r\ge 0$ let $R_r=1+B+\cdots+B^{r-1}$, with $R_0=0$. Among $R_0,\ldots,R_m$, two have the same residue modulo $m$, say $R_i$ and $R_j$ with $i<j$. Their difference is $B^iR_{j-i}$. As $\gcd(B,m)=1$, this yields $m\mid R_{j-i}$.

The integer $N=U R_{j-i}$ consists of $j-i$ consecutive copies of the block $U$. It is divisible by $h$ and $m$, hence by $n$. Its digit product is $P_b(U)^{j-i}$, a positive multiple of $n$. Repeating this entire numeral any positive number of times preserves both divisibilities and gives distinct witnesses. $\square$

## Example

For $n=14$ in decimal, the suffix $2$ already provides the factor $2$ in both the numeral and the digit product. Prepend $7$ to form the block $72$. Since $1+100+100^2=10101=7\cdot1443$, three copies give

$$
727272=14\cdot51948,\qquad P_{10}(727272)=(7\cdot2)^3=2744.
$$

The construction proves existence. A085124 separately gives the least witness, which for $n=14$ is $378$.

## Related work

N. S. used a suffix and a repeated block in 2016 to prove that every positive integer whose final digit is nonzero has a multiple containing only nonzero digits. The proof above extends that construction to every base. The prime-factor prefix imposes the additional divisibility of the digit product. [Mathematics Stack Exchange](https://math.stackexchange.com/q/2067752)

The block-repetition argument is classical. Kuhn and Vogt discuss multiples formed by repeating a prescribed digit string, with possible trailing zeros. [*Numbers Without Ones* (1992)](https://www.fq.math.ca/Scanned/30-1/kuhn.pdf)

De Koninck and Luca study divisibility by digit products. Their Proposition 1 allows zero digits and takes the product over nonzero digits only. Their Lemma 2 constructs decimal suffixes divisible by powers of two. [*Positive integers divisible by the product of their nonzero digits* (2007)](https://ems.press/content/serial-article-files/44556)
