# A389524: the weighted row counts Nathanson's orphans

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Result

We prove **Conjecture 2** of [OEIS A389524](https://oeis.org/A389524), for every positive integer n:

$$\boxed{\sum_{k=1}^{n} k\,T(n,k)=h(n),}$$

where T is the original recursively defined integer triangle and h is Nathanson's orphan-counting function [A274628](https://oeis.org/A274628). The source writes the equivalent reversed row order

$$\boxed{\sum_{k=1}^{n}T(n,n-k+1)(n-k+1)=h(n).}$$

Both versions are formal Lean theorems. The target h(n) is the cardinality of the actual set of nonnegative integer solutions

$$a b-c d=n,\qquad a>c\ge0,\qquad b>d\ge0.$$

The proof does not define h by a generating function or assume a formula for it. It proves finiteness and the required counting identities from these literal solutions.

The [earlier package](../A389524/README.md) proved Conjectures 1 and 3, the ordinary row sum and the diagonal formula. This extension proves **one additional recorded assertion** and thereby completes the three numbered conjectures in the preserved A389524 source. The other two assertions are not counted again.

The first weighted rows give 1, 4, 7, 13, 15, 26, agreeing with the beginning of A274628. For example, row 6 is (0,0,1,−2,−1,6), whose weighted sum is 3−8−5+36=26. These examples illustrate the universal theorem; no finite check is a proof premise.

## Original triangle and inherited bridge

The source's first column is

$$T(n,1)=\begin{cases}1,&n=1,\\0,&n\ne1.\end{cases}$$

For k≥2, T(n,k)=0 when n<k, while for n≥k,

$$T(n,k)=1+\sum_{i=1}^{k-1}T(n-i,k-1)-\sum_{i=1}^{n-1}T(n-i,k).$$

The reproduced `Triangle.lean` defines this recurrence over integers and derives the column polynomials. Define

$$R_0(x)=0,\qquad R_{k+1}(x)=1+(1-x^k)R_k(x).$$

Then

$$\boxed{T(n,k)=[x^n]\,x^kR_k(x)\qquad(k\ge1).}$$

This is the already checked theorem `A389524.triangle_eq_column`, proved from the source recurrence by strong induction. The present proof begins from that bridge. Negative triangle entries and the exceptional first column are retained.

Write d(n) for the number of positive divisors, σ(n) for their sum, and

$$C(n)=\sum_{t=1}^{n-1}d(t)d(n-t).$$

We prove separately that the weighted row and the literal orphan count both satisfy

$$\boxed{2h(n)=C(n)+3\sigma(n)-d(n).}$$

The two connections are developed below.

## 1. Count the literal orphan solutions

### Finiteness

For any orphan, b≥d+1 and a≥c+1. Consequently

$$n=ab-cd\ge a+d(a-c)\ge a,$$

and, symmetrically, n≥b. Thus a,b,c,d≤n. This bounds every coordinate and proves that the originally unbounded solution set is finite.

### Split off c=0

When c=0, one has ab=n and 0≤d<b. For each positive divisor b of n, the value a=n/b is forced, and d has b possible values. These solutions therefore contribute σ(n).

When c>0, put

$$x=a-c,\quad y=b,\quad z=c,\quad w=b-d.$$

These are positive integers satisfying

$$xy+zw=n,\qquad y\ge w.$$

Conversely, every such quadruple gives exactly one orphan with c>0:

$$a=x+z,\quad b=y,\quad c=z,\quad d=y-w.$$

The inequalities ensure d≥0 and b>d, and the determinant equation follows immediately. Thus this is a bijection.

The total number of positive quadruples xy+zw=n is C(n): choose t=xy from 1 through n−1, then choose an ordered factorization of t and of n−t.

Interchanging the two ordered factor pairs swaps the cases y>w and y<w. Let E(n) count the equality case y=w. Then

$$2\#\{(x,y,z,w):xy+zw=n,\ y\ge w\}=C(n)+E(n).$$

For equality, n=(x+z)y. For each divisor y of n, the positive pair (x,z) has n/y−1 choices. Hence

$$E(n)=\sum_{y\mid n}(n/y-1)=\sigma(n)-d(n).$$

Combining this with the c=0 contribution proves

$$2h(n)+d(n)=C(n)+3\sigma(n). \tag{1}$$

`Orphans.lean` formalizes all these bijections, including the unbounded solution structure, its finite instance, the involution exchanging the two factors, and the equal-factor boundary. Equation (1) is `Nathanson.orphan_formula` and covers every positive index required by OEIS.

## 2. A finite marked divisor identity

To obtain the weighted triangle sum, fix a bound N and work in the commutative ring

$$A=\mathbb Z[x]/(x^{N+1}).$$

Let q denote the class of x. Thus q^(N+1)=0, so all sums and products below are finite. Every 1−q^i with i≥1 is a unit, with inverse given by a finite geometric sum.

In a second polynomial variable z define

$$F_0(z)=0,\qquad F_{k+1}(z)=z\bigl(1+(1-q^k)F_k(z)\bigr).$$

Put r_k=F_k(1) and b_k=F'_k(1). Then

$$r_0=0,\qquad r_{k+1}=1+(1-q^k)r_k,$$

$$b_0=0,\qquad b_{k+1}=r_{k+1}+(1-q^k)b_k. \tag{2}$$

The r_k are precisely the images of the column polynomials R_k.

Define a block product

$$B(t,d)=\prod_{j=0}^{d-1}(1-q^{t+j}).$$

Induction on k gives

$$[z^{d+1}]F_k(z)=
\begin{cases}B(k-d,d),&k\ge d+1,\\0,&k<d+1.\end{cases}$$

Therefore, for

$$F(z)=\sum_{k=0}^{N}q^kF_k(z),$$

nilpotence permits the coefficient to be written

$$[z^{d+1}]F(z)=\sum_{t=0}^{N}q^{t+d+1}B(t+1,d).$$

The elementary product difference

$$B(t+1,d+1)-B(t,d+1)
=q^t(1-q^{d+1})B(t+1,d)$$

telescopes. Since B(0,d+1)=0 and B(N+1,d+1)=1,

$$\boxed{F(z)=\sum_{i=1}^{N}\frac{z^i q^i}{1-q^i}.} \tag{3}$$

Differentiating at z=1 proves

$$\sum_{k=1}^{N}q^k b_k
=\sum_{i=1}^{N}\frac{i q^i}{1-q^i}
=E_N(q), \tag{4}$$

where

$$D_N(q)=\sum_{i=1}^{N}\sum_{j=1}^{N}q^{ij},\qquad
E_N(q)=\sum_{i=1}^{N}\sum_{j=1}^{N}i q^{ij}.$$

The bounds on the geometric expansions are valid because higher powers vanish. Equation (3) is a finite marked form of the classical generalized divisor identity associated with Bressoud and Subbarao; the full telescoping argument is proved in Lean.

## 3. The second Uchimura moment

Let

$$M_r(q)=\sum_{k=1}^{N}k^r q^k\prod_{j=k+1}^{N}(1-q^j),\qquad r=1,2.$$

The reproduced `Uchimura.lean` proves M₁=D_N using a finite polynomial identity. Specifically, define

$$H(z)=\sum_{k=0}^{N}z^kq^k\prod_{j=k+1}^{N}(1-q^j),$$

$$G(z)=\prod_{i=1}^{N}(1-zq^i),\qquad
P=\prod_{i=1}^{N}(1-q^i).$$

Then HG=P, with P a unit. This identity is fully proved in that module by scaling z to qz and comparing coefficients.

At z=1, H(1)=1 and H'(1)=D_N. Differentiating HG=P twice, and using the product derivative for G, gives

$$H''(1)=D_N(q)^2+
\sum_{i=1}^{N}\left(\frac{q^i}{1-q^i}\right)^2.$$

Since M₂=H''(1)+H'(1),

$$M_2=D_N^2+\sum_{i=1}^{N}\frac{q^i}{(1-q^i)^2}.$$

Expanding each inverse by a finite weighted geometric sum gives

$$\sum_{i=1}^{N}\frac{q^i}{(1-q^i)^2}
=\sum_{i=1}^{N}\sum_{j=1}^{N}j q^{ij}
=E_N(q),$$

where the last equality exchanges i and j. We have thus proved the classical second-moment identity

$$\boxed{M_2=D_N^2+E_N.} \tag{5}$$

`Weighted.lean` proves this using only finite derivatives, ring identities, and geometric sums, without assuming a higher-moment theorem.

## 4. Recover the weighted row

Set f_k=k r_k−b_k. Equation (2) gives

$$f_{k+1}=k+(1-q^k)f_k.$$

Induction on N, using the finite product recurrences for M₁ and M₂, proves

$$2f_{N+1}=N(N+1)-(M_2-M_1),$$

and then

$$2\sum_{k=1}^{N}q^k f_k=M_2-M_1.$$

Define V_N=Σ_{k=1}^N kq^k r_k. By f_k=k r_k−b_k and (4),

$$2V_N=M_2-M_1+2E_N.$$

Substitution of M₁=D_N and (5) yields

$$\boxed{2V_N=D_N^2-D_N+3E_N.} \tag{6}$$

Choose N=n>0 and extract the coefficient of x^n in the quotient identity. The original column bridge identifies the left side with twice the weighted triangle row. On the right,

$$[x^n]D_n=d(n),\qquad [x^n]E_n=\sigma(n),\qquad
[x^n]D_n^2=C(n).$$

These coefficient formulas are also proved in Lean, using a weighted bijection between factor pairs and the literal positive divisors. Thus (6) gives

$$2\sum_{k=1}^{n}kT(n,k)=C(n)-d(n)+3\sigma(n).$$

Comparison with the independently proved orphan formula (1), followed by cancellation of 2 in the integers, proves the conjecture. Finally, the bijection k↦n−k+1 gives the exact reversed row ordering recorded by OEIS.

## Formal modules and scope

| File | Role |
|---|---|
| [Uchimura.lean](Uchimura.lean) | Reproduced dependency: finite first-moment identity and product machinery. |
| [Triangle.lean](Triangle.lean) | Reproduced dependency: literal triangle, derived columns, and the previously proved Conjectures 1 and 3. Only its historical header is clarified. |
| [Orphans.lean](Orphans.lean) | New module: literal orphan solution set, finiteness, explicit counting bijections, and divisor convolution. |
| [Weighted.lean](Weighted.lean) | New module: marked divisor identity, second moment, coefficient bridges, and Conjecture 2. |

Main declarations:

- `Nathanson.orphan_formula`: the literal orphan count and divisor convolution.
- `A389524Weighted.weighted_rows_nilpotent`: the complete finite polynomial identity (6).
- `A389524Weighted.weighted_row`: the weighted original row equals the literal orphan count.
- `A389524Weighted.original_conjecture`: the same theorem in the source's exact reversed finite ordering, for every n>0.

There are two new proof modules and two reproduced dependencies. This package counts one new resolved assertion. It does not claim the classical Uchimura or Bressoud–Subbarao identities, the orphan convolution formula, or the earlier Conjectures 1 and 3 as new discoveries. The contribution is the complete connection from the 2025 source recurrence to its conjectured orphan count, together with formal verification.

## Prior work and source status

The preserved A389524 revision 19 still records Conjecture 2 with verification through n=500. The A274628 revision 45 provides the literal orphan definition and earlier formulas. Both exact sources are included in [sources](sources).

Relevant primary literature includes:

- K. Uchimura, *An identity for the divisor generating function arising from sorting theory*, Journal of Combinatorial Theory, Series A 31 (1981), 131–135. [DOI](https://doi.org/10.1016/0097-3165(81)90009-1).
- D. M. Bressoud and M. V. Subbarao, *On Uchimura's connection between partitions and the number of divisors*, Canadian Mathematical Bulletin 27 (1984), 143–145. Equation (3) gives the generalized divisor weight; equation (8) records the higher-moment framework. [DOI](https://doi.org/10.4153/CMB-1984-022-5).
- Archit Agarwal, Subhash Chand Bhoria, Pramod Eyyunni, and Bibekananda Maji, *Bressoud–Subbarao type weighted partition identities for a generalized divisor function*, arXiv:2210.03457 (2022). Equations (1.5) and (1.9) explicitly record the two classical ingredients used here. [Primary manuscript](https://arxiv.org/pdf/2210.03457).
- [OEIS A274628](https://oeis.org/A274628), including David Radcliffe's 2019 solution-count interpretation and the pre-existing divisor/partition formulas. These formulas are proved from the original count in the present formalization.

Exact-identifier and semantic searches, a live check of the trureturing public index, and checks of the enumerated targets of *Low-Hanging Fruit* I–V did not locate an earlier resolution of this exact triangle-to-orphan statement. This is a bounded search finding, not a certification of historical priority or OEIS editorial acceptance. Full search scope and dependency provenance are in [source_checks.md](source_checks.md).

## Reproduce and verify

The package pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With that toolchain selected, run:

```sh
lake exe cache get
lake build
```

All four exact source modules have passed a fresh standalone package build and a separate independent compilation. Public theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No unfinished proof, custom axiom, external proof oracle, or `native_decide` call occurs.

[verification.txt](verification.txt) records the fresh package build. [AUDIT.md](AUDIT.md) and [audit-verification.txt](audit-verification.txt) record the independent mathematical and formal checks. `SHA256SUMS.txt` identifies the exact delivered artifacts.
