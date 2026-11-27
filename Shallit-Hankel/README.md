# Shallit’s shifted Hankel determinants

For Shallit's integer-alphabet Problem 43, an explicit word on $\{1,4,7\}$ has nonzero determinants of every odd order at every shift, and of every order at a prescribed shift. The paper determines the exact 3-adic valuation on a larger set of order–shift pairs. For each cutoff $R$ it also constructs a three-symbol alphabet in $[1,48R]$ working through order $R$ at every shift. [Integer-word manuscript and checks](integer-lifts.md)

For a word $w$, write $H_r(s)=\det(w_{s+i+j})_{0\le i,j<r}$. Shallit’s 2010 Oberwolfach article asks both about one particular four-letter word over the integers (Problem 44) and about every possible integer word modulo a fixed modulus (Conjecture 45). [Original problem statements, p. 2234](https://doi.org/10.4171/OWR/2010/37)

## Uniform bounds at every order and shift

For Shallit’s four-letter substitution word, each of the following finite sets of integer determinants has gcd one, for every $s\ge0$ and $r\ge1$.

| Fixed parameter | Determinants in the set |
|---|---|
| Order $r$ | $H_r(s+i)$ for $0\le i<\lceil13r/2\rceil$ |
| Shift $s$ | $H_k(s)$ for $r\le k\le\lfloor15r/2\rfloor$ |

Thus every prime has a nonzero determinant in each indicated interval, at every scale. The proof finds equal strings of preceding symbols with distinct next values differing by one. Such a pair contradicts a proposed linear recurrence over any field. A triangular Gram matrix and a separate sliding-minor argument turn the recurrence obstruction into the two bounds. Whether every individual integer determinant is nonzero remains open. [Proof manuscript](gcd.pdf) · [LaTeX](gcd.tex) · [Finite factor tables and independent sample gcds](verify_gcd.py) · [Recorded output](gcd-verification.txt)

## Sharp bounds for six moduli

The longest residue word whose shifted Hankel determinants are all nonzero has the following length. Every longer word, including every infinite word, has a vanishing minor modulo the specified modulus.

| Modulus | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|
| Maximum length | 2 | 4 | 24 | 22 | 42 | 52 |

The proof enumerates the complete normalized prefix trees. For the composite moduli it divides exact integer determinants. It uses field arithmetic for the four primes. A separate fraction-free elimination checks all 1,460 minors in the six attaining words and repeats the complete unnormalized searches for moduli two through five. The general modulus conjecture remains open. [Proof manuscript](moduli.pdf) · [LaTeX](moduli.tex) · [Complete search](verify_moduli.cpp) · [Extremizers and counts](moduli-verification.txt) · [Independent checks](check_moduli.py) · [Cross-check output](moduli-crosscheck.txt)

Run the new checks with Python 3.9 or later and a C++17 compiler supporting signed 128-bit integers.

~~~sh
python3 -B verify_gcd.py
c++ -O3 -std=c++17 verify_moduli.cpp -o /tmp/verify-shallit-moduli
/tmp/verify-shallit-moduli
python3 -B check_moduli.py
~~~

## All shifts through order 4096

**Blake Stone · Computation and proof developed with OpenAI Codex.**

Let $w=w_0w_1\ldots$ be the infinite word beginning with $1$ and fixed by the substitution

$$
\varphi(1)=12,\qquad \varphi(2)=23,\qquad
\varphi(3)=14,\qquad \varphi(4)=32.
$$

**Finite-order theorem.** For every starting position $s\ge0$ and every integer $1\le r\le4096$,

$$
H_r(s)=\det\big(w_{s+i+j}\big)_{0\le i,j<r}\ne0.
$$

Jeffrey Shallit asks whether this holds for every order in Problem 9 of his 2014 BCTCS lecture. The slides offer £50 for the problem and report checking a prefix of length 800. The result here covers every position of the infinite word for the stated finite range of orders. Orders beyond 4096 remain outside this proof. Shallit's separate three-real-number alphabet problem has since been solved by Claudemir de Souza Cavalcante. [Shallit, 2014 lecture, slides 33–35](https://cs.uwaterloo.ca/~shallit/Talks/bc4.pdf) · [Shallit's updates](https://cs.uwaterloo.ca/~shallit/talks.html)

## Why checking nine finite words covers every shift

The pairs of adjacent symbols in $w$ form the set

$$
\mathcal P=\{12,14,21,22,23,31,32,41,42\}.
$$

All nine occur in $\varphi^5(1)$. Each adjacent pair in an image word either lies inside a single letter's image or consists of the last letter of $\varphi(a)$ and the first of $\varphi(b)$ for an adjacent pair $ab$ in the preimage. The four individual images belong to $\mathcal P$, and the boundary operation sends every pair in $\mathcal P$ back into $\mathcal P$. This gives the asserted equality by induction on iterates of $\varphi$. The verifier checks occurrence and closure directly.

Now decompose $w=\varphi^{13}(w)$ into blocks of length $2^{13}=8192$. The entries of an order-$r$ Hankel matrix are determined by $2r-1$ consecutive symbols. For $r\le4096$, at most 8191 symbols are needed, so the determining factor lies in the union of two neighboring blocks. Every such union is $\varphi^{13}(ab)$ for one of the nine pairs $ab\in\mathcal P$. Each of the nine test words has length 16384. This proves that the finite computation below suffices for the theorem.

## Certificate computation

The [C++ verifier](verify.cpp) computes consecutive Hankel determinants modulo $P=2^{61}-1$. It initializes $H_0(s)=1$ and $H_1(s)=w_s$. The Desnanot–Jacobi identity gives, for $r\ge2$,

$$
H_r(s)H_{r-2}(s+2)
=H_{r-1}(s)H_{r-1}(s+2)-H_{r-1}(s+1)^2.
$$

The minor on the left removes the first and last rows and columns, which shifts the starting index by two. The program verifies each required row-product inverse before division. Induction on $r$ therefore gives the actual determinant residues. A nonzero residue certifies a nonzero integer determinant.

The verifier tests every legal offset at each order in each test word, for

$$
9\sum_{r=1}^{4096}(16384-2r+2)=453021696
$$

nonzero residues. This total counts window occurrences, including repeated factors. As an independent check of the recurrence and indexing, the program also evaluates the signed permutation formula in ordinary integer arithmetic for every order from 1 through 8 at all offsets of the nine words $\varphi^4(ab)$. All 1800 direct values agree with the modular computation.

Compile with a C++17 compiler supporting 128-bit unsigned multiplication (GCC or Clang on a 64-bit target).

~~~sh
g++ -O3 -std=c++17 verify.cpp -o verify
./verify
~~~

The reference run took about 4.3 seconds after compilation. Its final two lines were:

~~~
Independent direct checks: 1800
Nonzero modular determinants: 453021696
~~~
