# A129453: the binomial quotient is an integer square

Blake Stone, developed with OpenAI Astra 6.2. November 26, 2026.

Let

$$
G(n)=\prod_{i=1}^{n}\prod_{j=1}^{n}\gcd(i,j),\qquad G(0)=1,
$$

and let

$$
T(n,k)=\frac{G(n)}{G(k)G(n-k)},\qquad 0\le k\le n.
$$

[OEIS A129453](https://oeis.org/A129453), introduced by Peter Bala on April 16, 2007, suggests that the entries are integers divisible by $\binom nk$, with quotient an integer square. This package proves the full square refinement, directly from the displayed double gcd product:

$$
\boxed{\quad
\forall n\ge0,\ 0\le k\le n,\quad
\exists t\in\mathbb N:\quad
G(n)=\binom nk\,G(k)G(n-k)t^2.
\quad}
$$

In particular the original rational value of $T(n,k)$ is exactly $\binom nk\,t^2$. The theorem clears all denominators, so integrality is established and cannot result from rounded natural-number division.

## Proof

Write $m=n-k$, fix a prime $p$, and let $v_p$ denote its exponent in a positive integer. Counting ordered pairs whose two entries are multiples of $p^r$ gives the known formula

$$
v_p(G(u))=\sum_{r\ge1}\left\lfloor\frac{u}{p^r}\right\rfloor^2.
$$

Legendre's formula similarly gives

$$
v_p(u!)=\sum_{r\ge1}\left\lfloor\frac{u}{p^r}\right\rfloor.
$$

For each $r$, put

$$
x_r=\left\lfloor\frac{n}{p^r}\right\rfloor,\quad
y_r=\left\lfloor\frac{k}{p^r}\right\rfloor,\quad
z_r=\left\lfloor\frac{m}{p^r}\right\rfloor.
$$

Since $n=k+m$, there is a carry $c_r\in\{0,1\}$ such that $x_r=y_r+z_r+c_r$. Expanding the square gives

$$
x_r^2-y_r^2-z_r^2-(x_r-y_r-z_r)
=2\bigl(y_rz_r+c_r(y_r+z_r)\bigr).
$$

The binomial factorial identity therefore yields

$$
\begin{aligned}
v_p(G(n))
&-v_p(G(k))-v_p(G(m))-v_p\!\left(\binom nk\right)\\
&=2\sum_{r\ge1}\bigl(y_rz_r+c_r(y_r+z_r)\bigr).
\end{aligned}
$$

The right side is a nonnegative even integer. Thus $\binom nk G(k)G(m)$ divides $G(n)$, and every prime exponent of the quotient is even. Unique prime factorization makes that quotient an integer square, proving the assertion. All sums and products are finite: the floor terms vanish once $p^r>n$. When $n=0$, all products are empty and the theorem holds with $t=1$.

This also gives an explicit square root:

$$
t=\prod_{p\ \mathrm{prime}}
p^{\sum_{r\ge1}(y_rz_r+c_r(y_r+z_r))}.
$$

For example, $T(4,2)=24=\binom42\cdot2^2$, and $T(6,3)=11520=\binom63\cdot24^2$.

## Formal verification

`Proof.lean` defines `gcdProduct n` using the original gcd product over `i,j=1,...,n`. It proves the valuation formula by finite double counting, rather than taking that formula as an extra hypothesis. It also proves the needed factorial valuation formula and the carry identity. The exact denominator-cleared result is:

```lean
theorem square_quotient (n k : ℕ) (hk : k ≤ n) :
    ∃ t : ℕ, gcdProduct n =
      n.choose k * gcdProduct k * gcdProduct (n-k) * t^2
```

The corollaries `conjecture`, `binomial_dvd`, and `quotient_square` state respectively that the triangle term is a binomial coefficient times a square, that the binomial coefficient divides it, and that its exact quotient is a square.

The source has no `sorry`, additional axiom, `native_decide`, or bounded-range restriction. Every index $n\ge0$ and $0\le k\le n$, including the boundary entries, is covered. The only reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Prior work and source status

The [A129453 internal entry](https://oeis.org/A129453/internal), revision 9 dated February 7, 2024, retains the suggested integer-square property. The new assertion addressed here is the square refinement; the underlying sequence and several ingredients are prior work:

- [A092287](https://oeis.org/A092287) credits Charles R. Greathouse IV (April 2, 2013) with confirming its squared-floor prime-valuation formula. Daniel Forgues (April 8, 2013) supplies $G(n)=n!\,H(n)^2$, where $H$ is the triangular gcd product.
- [A224479](https://oeis.org/A224479) records that triangular product and its valuation $v_p(H(n))=\sum_{r\ge1}\binom{\lfloor n/p^r\rfloor}{2}$. This gives another route to the square refinement once one proves the necessary divisibility of triangular products.
- Wanli Ma, [*Generalized factorials characterized by Dirichlet convolution*, arXiv:2509.13354 (2025)](https://arxiv.org/abs/2509.13354), Theorem 2.5 and the example on pp. 6–7, proves that $G$ is a generalized factorial. This already establishes ordinary integrality of $T(n,k)$, and that fact is not claimed as a new result here. The paper does not state the integer-square refinement proved above.

Searches on November 26, 2026 covered the sequence identifiers, the equivalent triangular gcd product, binomial-square terminology, the cited generalized-factorial paper, and the public proof indexes of [trureturing](https://www.trureturing.org/conjectures), [Fabian Arevalo](https://fabianarevalo.com/math), and [Eppie](https://github.com/Eppie/oeis-proofs). No earlier explicit proof of the selected square refinement was located. This is a bounded source-status search, not a claim of absolute publication priority.

## Reproduce

The package pins Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With Lean's `elan` toolchain manager installed:

```sh
lake exe cache get
lake build
```

`verification.txt` records a successful build of the actual standalone package. The independent audit and its compiler log are in `AUDIT.md` and `audit-verification.txt`.

## Collected proof document

[Read the complete proof collection (PDF)](../notes/Math_Proofs_Batch4.pdf) · [LaTeX source](../notes/Math_Proofs_Batch4.tex)
