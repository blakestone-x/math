# Four is the maximum number of consecutive prime rotate-and-add steps

Blake Stone · Proof developed with OpenAI Codex

For a positive integer $x$, split its decimal expansion into two equal-length outer blocks and, for odd length, a single middle digit. Interchange the blocks while leaving the middle digit in place. Denote the resulting integer by $\operatorname{rot}(x)$ and set $F(x)=x+\operatorname{rot}(x)$. Initial zeros in the rotated string have their usual numerical value. [OEIS A086002](https://oeis.org/A086002)

**Theorem.** No prime $x$ has all five of $F(x),F^2(x),F^3(x),F^4(x),F^5(x)$ prime. Four successive prime outputs are attainable.

This proves the second conjecture in Chuck Seggelin's A086004. Chai Wah Wu had exhibited four-step examples and ruled out six successive steps. One of Wu's examples, with the starting prime first, is

$$
10010905789,\quad15800815799,\quad31600631599,\quad
63200263199,\quad126399526399.
$$

[OEIS A086004](https://oeis.org/A086004) · [Chai Wah Wu, OEIS A261458](https://oeis.org/A261458)

## The middle digit controls oddness two steps later

Write $x_i=F^i(x)$. Suppose that $x_0,\ldots,x_5$ are all prime. A single-digit prime immediately doubles to a composite. An even-length prime $x_i=10^k A+B$ gives

$$
F(x_i)=(10^k+1)(A+B).
$$

Both factors exceed one, since the leading block is positive and the last digit of an even-length prime is nonzero. This is R. J. Mathar's observation in A086004. Consequently $x_0,\ldots,x_4$ all have odd length at least three. A rotate-and-add step never decreases the length and increases it by at most one. Thus these five inputs all have the same length $2k+1$, with $k\ge1$.

Put $u=10^k$. For $i=0,\ldots,4$, write $x_i=10uA_i+uC_i+B_i$, where $C_i\in\{0,\ldots,9\}$ is the middle digit, and put $S_i=A_i+B_i$. The rotation swaps $A_i$ and $B_i$, giving

$$
x_{i+1}=(10u+1)S_i+2uC_i .
$$

In particular, $x_{i+1}$ has the parity of $S_i$. Since $x_1,\ldots,x_5$ are primes greater than $2$, all five of $S_0,\ldots,S_4$ must be odd.

For $i=0,\ldots,3$, the output still has length $2k+1$. Thus $S_i<u$, since otherwise the displayed expression would reach $10u^2=10^{2k+1}$. Reading off its right block and carrying the doubled middle digit into its left block gives

$$
B_{i+1}=S_i,\qquad
C_{i+1}=2C_i\bmod 10,\qquad
A_{i+1}=S_i+\lfloor C_i/5\rfloor.
$$

It follows that $S_{i+1}=2S_i+\lfloor C_i/5\rfloor$. Oddness of $S_{i+1}$ requires $C_i\ge5$. Therefore $C_0,C_1,C_2,C_3$ would all have to be at least $5$ under successive doubling modulo ten. This is impossible. Starting from $5,6,7$ leads immediately to $0,2,4$, respectively. Starting from $8$ gives $8,6,2$, and starting from $9$ gives $9,8,6,2$. The contradiction proves the upper bound. Wu's example attains it. $\square$
