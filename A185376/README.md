# Necklaces admitting a palindromic cut

Research notes for Blake Stone. Proof developed with OpenAI Codex.

A necklace identifies words that differ by a cyclic rotation. Tony Bartoletti proposed a formula for the binary necklaces of even length that can be cut to read the same in both directions. The argument below derives it for any alphabet size and also allows prescribed color counts. The one-or-two-palindromes classification used here is due to Chuan Guo, Jeffrey Shallit and Arseny M. Shur, Section 2 of their 2015 paper. [OEIS A185376](https://oeis.org/A185376) · [OEIS A185333](https://oeis.org/A185333) · [Guo, Shallit and Shur](https://arxiv.org/abs/1503.09112)

**Theorem.** For $q\ge1$ colors and $N\ge1$ beads, write $h$ for the largest odd divisor of $N$. The number of necklaces having a palindromic cut is

$$
P_q(N)=\frac{q^{\lceil N/2\rceil}+q^{(h+1)/2}}{2}.
$$

In particular if $N=2n$ and $n=2^t h$ with $h$ odd, the binary answer is $2^{n-1}+2^{(h-1)/2}$, exactly Bartoletti's expression.

**Proof.** Start with a palindromic word $w$. Let $r$ rotate it by one place and let $d$ be its least positive rotational period, so $d\mid N$. Reversal sends $r^jw$ to $r^{-j}w$. These words coincide exactly when $d\mid 2j$. Among the $d$ distinct rotations there are therefore $\gcd(2,d)$ distinct palindromes.

There are $H=q^{\lceil N/2\rceil}$ labeled palindromes. Those with odd rotational period are precisely the ones fixed by $r^h$, since $d$ is odd exactly when $d\mid h$. Such a word repeats a block of length $h$, and the repeated word is palindromic exactly when that block is palindromic. This gives $J=q^{(h+1)/2}$ labeled palindromes of odd period. They contribute one necklace each. The other $H-J$ palindromes contribute one necklace per pair. Their total is $(H+J)/2$. ∎

**Prescribed color counts.** For multiplicities $\mathbf c=(c_1,\dots,c_q)$ totaling $N$, let $M(\mathbf c)$ count labeled palindromes of this content. It vanishes unless the number of odd $c_i$ is $N\bmod 2$. Otherwise the middle letter, when present, is forced, and arranging the first half gives

$$
M(\mathbf c)=\frac{\lfloor N/2\rfloor!}{\prod_i\lfloor c_i/2\rfloor!}.
$$

Put $u=N/h$. The same counting proof gives $(M(\mathbf c)+M(\mathbf c/u))/2$ necklaces of that content. Interpret the second term as zero if any multiplicity is indivisible by $u$. Indeed, an odd-period palindrome is exactly $u$ copies of a palindromic block of content $\mathbf c/u$.

For four binary beads, for instance, the three qualifying necklaces are represented by $0000,0110,1111$. The middle one has two distinct palindromic cuts as words, $0110$ and $1001$. The verifier enumerates necklaces directly and checks each content separately. [Exact enumeration](verify.py)
