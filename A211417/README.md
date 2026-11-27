# A211417: the complete positive-shift integrality family

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

## The result

Let

$$
A(n)=\frac{(30n)!\,n!}{(15n)!\,(10n)!\,(6n)!},\qquad n\ge0.
$$

For every $k\in\{2,3,5\}$, every integer $r\ge0$, and every $n\ge0$,

$$
\boxed{\quad
\prod_{\substack{1\le i\le r\\\gcd(i,k)=1}}(kn+i)
\ \mid\ ((30r)!)^r A(n).
\quad}
$$

Consequently, the positive constant

$$
C(k,r)=((30r)!)^r
$$

works in Peter Bala's entire positive-shift integrality conjecture in the COMMENTS of [OEIS A211417](https://oeis.org/A211417), dated August 28, 2025. The source asks for all $r\ge1$; the proof also handles $r=0$, when both the product and the constant are 1. The same constant works for all three permitted values of $k$.

This is a resolution of that one generalized assertion. The original integrality of $A(n)$, the four fixed-factor assertions involving $2n+1,3n+1,5n+1$, and the separate negative-shift $D(r)$ family have prior proofs. They are credited in [source_checks.md](source_checks.md) and are not claimed as new here. The displayed constant is explicit and sufficient; optimal constants are not determined.

## Proof

### 1. The factorial contribution

For positive integers $m$, set

$$
F(n,m)=\left\lfloor\frac{30n}{m}\right\rfloor
+\left\lfloor\frac n m\right\rfloor
-\left\lfloor\frac{15n}{m}\right\rfloor
-\left\lfloor\frac{10n}{m}\right\rfloor
-\left\lfloor\frac{6n}{m}\right\rfloor.
$$

Put $t=\lfloor30n/m\rfloor$. Nested integer division gives the exact identity

$$
F(n,m)=f(t),\qquad
f(t)=t+\lfloor t/30\rfloor-\lfloor t/2\rfloor
-\lfloor t/3\rfloor-\lfloor t/5\rfloor.
$$

The integer function $f$ has period 30. On residues $0,\ldots,29$, its values are

```
0, 1, 1, 1, 1, 1, 0, 1, 1, 1,
0, 1, 0, 1, 1, 0, 0, 1, 0, 1,
0, 0, 0, 1, 0, 0, 0, 0, 0, 1.
```

In particular $F(n,m)\ge0$. Legendre's formula shows that the exponent of each prime in the numerator of $A(n)$ is at least its exponent in the denominator. Hence $A(n)$ is a positive integer, and

$$
v_p(A(n))=\sum_{e\ge1}F(n,p^e).
$$

The known integrality of this factorial ratio is reproduced as part of the formal connection to the source definition. Lean checks the floor inequality by Presburger arithmetic, not by assuming it as an external lemma.

### 2. A large divisor contributes one

Fix $k\in\{2,3,5\}$, an integer $i\ge1$ with $\gcd(i,k)=1$, and $m>30i$ such that $m\mid kn+i$. Write

$$
kn+i=mj,\qquad d=30/k.
$$

If $k\mid j$, the displayed equality would imply $k\mid i$, contradicting coprimality. Therefore $j\not\equiv0\pmod k$. Multiplying by $d$ gives

$$
30n+di=mdj.
$$

Since $0<di<m$,

$$
\left\lfloor\frac{30n}{m}\right\rfloor=dj-1.
$$

This leaves precisely seven possible residues for $t$ modulo 30:

| $k$ | Nonzero residues of $j\pmod k$ | Residues of $t\pmod{30}$ |
|---|---|---|
| 2 | 1 | 14 |
| 3 | 1, 2 | 9, 19 |
| 5 | 1, 2, 3, 4 | 5, 11, 17, 23 |

Every residue in the last column has $f(t)=1$. Thus

$$
m>30i,\quad m\mid kn+i,\quad\gcd(i,k)=1
\quad\Longrightarrow\quad F(n,m)=1.
$$

The formal proof derives the quotient identity before using arithmetic to check these cases. It does not replace the original sequence by a guessed recurrence or a numerical table.

### 3. Controlling the whole product

Set

$$
S=\{i:1\le i\le r,\ \gcd(i,k)=1\},\qquad
N_m=\#\{i\in S:m\mid kn+i\}.
$$

If $m>30r$, there can be at most one such $i$: two distinct indices would give $m\mid i-j$ with $0<|i-j|<m$. When an index exists, the previous step gives $F(n,m)=1$. Hence

$$
N_m\le F(n,m)\qquad(m>30r).
$$

If $m\le30r$, use $N_m\le|S|\le r$ and $\lfloor30r/m\rfloor\ge1$. Together with $F(n,m)\ge0$, this gives the uniform estimate

$$
N_m\le F(n,m)+r\left\lfloor\frac{30r}{m}\right\rfloor
\qquad(m\ge1).
$$

Now fix any prime $p$ and sum this inequality for $m=p^e$, $e\ge1$. Counting every prime-power divisibility gives the valuation of the full product, including repeated prime factors in different linear factors:

$$
\begin{aligned}
v_p\!\left(\prod_{i\in S}(kn+i)\right)
&=\sum_{e\ge1}N_{p^e}\\
&\le\sum_{e\ge1}F(n,p^e)
+r\sum_{e\ge1}\left\lfloor\frac{30r}{p^e}\right\rfloor\\
&=v_p(A(n))+r\,v_p((30r)!)\\
&=v_p\bigl(((30r)!)^r A(n)\bigr).
\end{aligned}
$$

The inequality for every prime proves the stated divisibility. All sums are finite because their terms vanish for sufficiently large prime powers. The formal proof uses an explicit finite common cutoff exceeding $30n$, $30r$, and $kn+r$.

## The formal statement and source connection

[Proof.lean](Proof.lean) uses natural-number factorials for the numerator and denominator. Its natural-number quotient `a` is justified by the exact identity

```lean
theorem factorial_ratio_identity (n : ℕ) :
  a n * denominator n = numerator n
```

The literal rational factorial ratio is separately defined as `sourceRatio`; `sourceRatio_eq_a` proves that it equals the cast of `a`. The main endpoints are:

| Theorem in `ChebyshevShifts` | Meaning |
|---|---|
| `cross_divisibility` | The product times the original factorial denominator divides the constant times the numerator. |
| `factorial_ratio_integral` | The original factorial denominator divides the numerator. |
| `factorial_ratio_identity` | Natural division is exact. |
| `sourceRatio_eq_a` | The literal rational ratio equals the integral sequence. |
| `positive_shift_divisibility` | The explicit constant clears the full product for all indices. |
| `bala_positive_shift_conjecture` | A positive integer constant exists, uniformly in $n$. |
| `positive_shift_rational_integrality` | The source's rational expression is equal to an integer. |

There are no unproved auxiliary hypotheses, finite cutoffs on the theorem, additional axioms, or uses of `sorry`, `admit`, `unsafe`, or `native_decide`. The checked endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction

The package pins Lean **4.19.0** and mathlib commit **c44e0c8ee63ca166450922a373c7409c5d26b00b**. With the normal Lean toolchain installed:

```sh
lake exe cache get
lake build
```

The author build is recorded in [verification.txt](verification.txt). The independent source and theorem review is recorded in [AUDIT.md](AUDIT.md), with a separate fresh build in [audit-verification.txt](audit-verification.txt). Local proof objects are excluded from the package; the verification builds compile the proof source afresh against the pinned external dependency cache.

The exact OEIS export is archived in [sources/A211417.seq](sources/A211417.seq). The mathematical section for the combined manuscript is [manuscript-section.tex](manuscript-section.tex).
