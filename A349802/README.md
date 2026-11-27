# Euler transforms of Lyndon words with prescribed initial zeros

Research notes for Blake Stone. Proof developed with OpenAI Codex.

For an alphabet consisting of $0$ and $q\ge1$ larger letters, let $L_q(n,k)$ be the number of length-$n$ Lyndon words that start with exactly $k$ zeros. A Lyndon word is the lexicographically least representative of a primitive necklace, a circular word with no shorter period. A349802 is the binary case $q=1$.

**Theorem.** For each $k\ge1$, the Euler transform of column $k$, indexed by word length, is

$$
\prod_{n\ge1}(1-x^n)^{-L_q(n,k)}
=\frac{1}{(1-x)^{\mathbf{1}_{\{k=1\}}}}
  \frac{1-q(x+\cdots+x^k)}{1-q(x+\cdots+x^{k+1})}.
$$

For a binary alphabet and $k=1$ this is $1/(1-x-x^2)$, with coefficients $1,1,2,3,5,\ldots$ from degree zero. For $k\ge2$ it is

$$
1+\frac{x^{k+1}}{1-x-x^2-\cdots-x^{k+1}}.
$$

Hence the coefficients in degrees 1 through $k$ are zero, the coefficient in degree $k+1$ is one, and subsequent coefficients follow the $(k+1)$-step Fibonacci recurrence. For example, column 2 gives $0,0,1,1,2,4,7,\ldots$ from degree one. This fixes the initial indexing in the conjecture.

## Proof

In any primitive necklace containing a zero and a nonzero letter, the least rotation begins with a longest circular run of zeros. Indeed a rotation with fewer initial zeros loses at the first letter where its rival still has a zero.

For necklaces containing at least one nonzero letter, cut the circle just after each nonzero letter. Circular zero runs of length at most $k$ correspond to a circular list of blocks $0^j b$, where $0\le j\le k$ and $b$ is one of the $q$ nonzero letters. This is bijective up to cyclic rotation. It preserves primitivity because any rotational symmetry permutes the nonzero letters and hence the cuts, while a repeated block list gives a repeated original word. There are $q$ block choices of each weight from 1 to $k+1$.

For a finite alphabet of blocks with weight enumerator $S(x)$, the product of $(1-x^{w(C)})^{-1}$ over all primitive block necklaces $C$ of weight $w(C)$ equals $1/(1-S(x))$. To see this, sum $S(x)^r/r$ over $r\ge1$. A primitive cycle of $\ell$ blocks repeated $h$ times has $\ell$ distinct rotations and contributes $x^{h w(C)}/h$ at $r=h\ell$. Summing over repetitions and exponentiating proves the product identity in formal power series.

Apply it first to maximum run at most $k$, with $S(x)=q(x+\cdots+x^{k+1})$, then to maximum run at most $k-1$. Dividing the two products retains exactly the necklaces whose maximum zero run is $k$. The only missing primitive all-zero necklace is the one-letter word $0$. It contributes $(1-x)^{-1}$ precisely in column 1. This proves the theorem for every alphabet size. ∎

**Sources.** The binary conjecture appears in Peter Kagey's [OEIS A349802](https://oeis.org/A349802). Andrew Howroyd's 2021 program in the same entry already encodes the binary relation using Möbius inversion. Peter Luschny records the companion inverse transforms in [A349903](https://oeis.org/A349903). The Fibonacci special case also appears in [A006206](https://oeis.org/A006206).

[Direct enumeration and exact Euler-product checks](verify.py)

Run `python3 verify.py` in this directory. It generates Lyndon words by testing every rotation and checks all columns through lengths 15, 10, and 8 for alphabets of sizes 2, 3, and 4, respectively.
