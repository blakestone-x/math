# Which digit sums occur in zero-free Harshad numbers?

Blake Stone · Proof developed with OpenAI Astra 6.2

A Harshad number is a positive integer divisible by the sum of its decimal digits. Amarnath Murthy's sequence A077754 asks for the least such integer of at least two digits, with no digit zero and with prescribed digit sum $n$. It records zero when no witness exists. In November 2002 Murthy conjectured the following classification. [OEIS A077754](https://oeis.org/A077754)

**Theorem.** A positive integer $n$ is the digit sum of a zero-free Harshad number with at least two digits if and only if $10\nmid n$ and $n\notin\{1,2,5,11\}$.

The construction uses decimal blocks whose digit sums all equal six. Choosing different blocks changes the residue of the numeral while leaving its digit sum fixed.

## A residue lemma

Let

$$
A=\{0,1,2,3,11,12,13,22,23,33\}.
$$

For $Q\ge1$ coprime to $10$, if $k\ge12$ and $9k+1\ge Q$, then every residue modulo $Q$ is representable as

$$
\sum_{i=0}^{k-1}1000^i x_i,\qquad x_i\in A.
$$

**Proof.** In $G=\mathbb Z/Q\mathbb Z$, let $S$ be the set of the indicated sums, and let $H=\{g\in G:S+g=S\}$ be its stabilizer. The image of $S$ in $G/H$ has trivial stabilizer. Each partial sumset there also has trivial stabilizer, since a translation preserving it preserves the final sumset.

When a sumset $X+Y$ has trivial stabilizer, Kneser's addition theorem gives $|X+Y|\ge |X|+|Y|-1$. Apply it successively in $G/H$, a cyclic group of order $d=[G:H]$. Each $1000^i$ is a unit modulo $d$, so all summands have the same image size $|A\bmod d|$. This gives

$$
|S\bmod H|\ \ge\ 1+k(|A\bmod d|-1).
$$

For $d>33$ all ten elements of $A$ are distinct modulo $d$, so the right side is $1+9k\ge Q\ge d$. For $4\le d\le33$, the elements $0,1,2,3$ remain distinct, giving at least $1+3k\ge37>d$. For $d\le3$, the first summand alone covers the quotient. Thus the image of $S$ is the whole quotient. Since $S$ is a union of $H$-cosets, $S=G$. $\square$

## Construction for $n\ge100$

Suppose $10\nmid n$. Factor $n=p^a m$, where $\gcd(m,10)=1$ and $p$ is the one prime among $2,5$ dividing $n$. If neither divides $n$, take $p=2$, $a=0$, and $m=n$.

Choose an $a$-digit suffix $v$ divisible by $p^a$, using digits $1,\ldots,p$. Starting with $v_0=0$, suppose $p^j\mid v_j$. A digit $u\in\{1,\ldots,p\}$ can be chosen to satisfy

$$
\frac{v_j}{p^j}+u(10/p)^j\equiv0\pmod p,
$$

because $10/p$ is a unit modulo $p$. Prepending $u$ gives $v_{j+1}=v_j+u10^j$ with $p^{j+1}\mid v_{j+1}$. Use an empty suffix for $a=0$.

Its digit sum $s$ satisfies $s\le n/4$. Indeed, for $p=2$ and $a\ge6$ one has $8a\le2^a$. For $p=5$ and $a\ge3$ one has $20a\le5^a$. Both inequalities follow by induction from the first exponent shown, and in the remaining cases $s\le pa\le10$. Put

$$
k=\left\lfloor\frac{n-s}{6}\right\rfloor,\qquad r=n-s-6k.
$$

Then $k\ge\lfloor n/8\rfloor\ge12$, and $1+9k\ge n$ because $1+9\lfloor n/8\rfloor\ge1+9(n-7)/8\ge n$ for $n\ge100$.

Build a numeral from the leading digit $r$ if $r>0$, followed by $k$ three-digit blocks, followed by the suffix $v$. Choose every block from the ten three-digit numbers with positive digits summing to six. Their values are precisely

$$
114+9A=\{114,123,132,141,213,222,231,312,321,411\}.
$$

Every resulting numeral has digit sum $n$, is divisible by $p^a$, and has only positive digits. It remains to make it divisible by $m$.

Let $C$ be the numeral using only blocks $114$. For $g=\gcd(9,m)$, the decimal digit-sum congruence gives $C\equiv n\equiv0\pmod g$. Write $Q=m/g$. The different block choices give all values

$$
C+9\cdot10^a\sum_{i=0}^{k-1}1000^i x_i,\qquad x_i\in A.
$$

After division by $g$, the coefficient $(9/g)10^a$ is a unit modulo $Q$. The residue lemma applies since $Q\le n\le 1+9k$. Some choice is consequently divisible by $m$ (automatically when $Q=1$). Divisibility by $p^a m=n$ follows.

## The exceptions and the finite check

A multiple of $10$ must end in zero. A numeral with two or more nonzero digits has digit sum at least two. The only such numeral of digit sum two is $11$, which is odd. A zero-free multiple of five ends in five, exhausting a digit sum of five before the other digits can be supplied. Finally, for digit sum eleven, the alternating digit sum is odd and has absolute value at most nine, since each parity of positions has a positive subtotal. Such a numeral cannot be divisible by eleven.

For $1\le n<100$, the adjoining verifier exhausts the possible digit sums and residues. It initializes all two-digit words with positive digits and digit sum at most $n$. From each state $(s,t)$, appending a digit $u$ gives $(s+u,(10t+u)\bmod n)$. Every eligible numeral is obtained this way and the sum strictly increases, so a single pass in increasing $s$ suffices. The missing indices are exactly

$$
1,2,5,10,11,20,30,40,50,60,70,80,90.
$$

This verifies every case below the construction's threshold and completes the proof. [Finite-case verifier](verify.py)

## References

- Amarnath Murthy, OEIS A077754 (2002), with a table through $n=100$ by Chai Wah Wu. [Sequence entry](https://oeis.org/A077754)
- Matt DeVos, *A short proof of Kneser's addition theorem for abelian groups* (2013). [arXiv:1303.3539](https://arxiv.org/abs/1303.3539)
- N. S., decimal construction of a zero-free suffix divisible by $2^a$ or $5^a$ (2016 answer and 2017 comment). [Mathematics Stack Exchange](https://math.stackexchange.com/q/2067752)
