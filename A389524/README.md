# A389524: divisor row sums and a divisor-count diagonal

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Results

For the triangle defined in [OEIS A389524](https://oeis.org/A389524), we prove **Conjectures 1 and 3** for every positive integer n:

\[
\sum_{k=1}^{n} T(n,k)=d(n),
\qquad
T(2n,n)=n-d(n),
\]

where d(n) is the number of positive divisors of n, [A000005](https://oeis.org/A000005). The second right-hand side is exactly [A049820](https://oeis.org/A049820).

The formal proof defines the original recursive triangle first and derives its generating polynomials. It then proves the needed finite form of **Uchimura's classical divisor identity**, including the connection to the literal set of positive divisors. Neither displayed assertion is assumed as a property of an alternative sequence.

The entry's **Conjecture 2**, involving a weighted row sum and Nathanson's orphan-counting function A274628, is not proved or counted in this package. There are two resolved assertions in one OEIS entry.

## Exact recursive definition

The source program specifies

\[
T(n,1)=\begin{cases}1,&n=1,\\0,&n\ne1,\end{cases}
\]

and, for k≥2,

\[
T(n,k)=0\quad(n<k),
\]

\[
T(n,k)=1+\sum_{i=1}^{k-1}T(n-i,k-1)
          -\sum_{i=1}^{n-1}T(n-i,k)\quad(n\ge k).
\]

The Lean definition uses integers for the entries, so negative entries are preserved. In the second sum it reindexes n−i as j, giving the same sum over j=1,…,n−1. It sets the unused auxiliary column k=0 to zero. Every recursive call has a strictly smaller first index, and Lean checks termination.

The first rows are

\[
(1),\quad(0,2),\quad(0,-1,3),\quad(0,0,-1,4),\quad(0,0,-2,-1,5).
\]

Their row sums are 1,2,2,3,2, agreeing with d(1),…,d(5).

## Proof

### 1. Derive the column polynomials

All series in this step are formal. Extend T(n,k) by zero at negative n, and write

\[
C_k(x)=\sum_{n\ge0}T(n,k)x^n.
\]

The first column gives C₁(x)=x. Moving the second sum in the recurrence to the left, and then taking generating series, gives for k≥2

\[
\frac{C_k(x)}{1-x}
=\frac{x^k}{1-x}+(x+x^2+\cdots+x^{k-1})C_{k-1}(x).
\]

Consequently

\[
C_k(x)=x^k+x(1-x^{k-1})C_{k-1}(x).
\]

Define polynomials R₀(x)=0 and

\[
R_{k+1}(x)=1+(1-x^k)R_k(x).
\]

Then R₁(x)=1 and C_k(x)=x^kR_k(x). In particular, each column generating series is a polynomial. The Lean theorem `triangle_eq_column` establishes this connection by strong induction on the original row index, using finite coefficient sums rather than assuming a generating-function manipulation.

### 2. Express the sum of columns as a weighted product sum

Put

\[
S_N(x)=\sum_{k=1}^{N}x^kR_k(x),
\qquad
W_N(x)=\sum_{k=1}^{N}k x^k\prod_{j=k+1}^{N}(1-x^j).
\]

The recurrence for R gives

\[
R_{k+1}-R_k=1-x^kR_k.
\]

Summing this identity yields

\[
R_{N+1}=N+1-S_N.
\]

It follows that

\[
S_{N+1}=(1-x^{N+1})S_N+(N+1)x^{N+1}.
\]

The product definition of W gives exactly the same recurrence, and S₀=W₀=0. Therefore S_N=W_N for every N. These identities are formalized as `Uchimura.recurrence_tail` and `Uchimura.recurrence_rows`.

### 3. A finite proof of the required Uchimura identity

We prove

\[
W_N(x)\equiv
\sum_{i=1}^{N}\sum_{j=1}^{N}x^{ij}
\pmod{x^{N+1}}.\tag{1}
\]

This is the finite coefficient form needed here of Uchimura's classical identity

\[
\sum_{k\ge1}k x^k\prod_{j>k}(1-x^j)
=\sum_{i\ge1}\frac{x^i}{1-x^i}.
\]

For a self-contained finite proof of (1), work in the commutative ring

\[
A=\mathbb Z[x]/(x^{N+1}),
\]

and let q be the class of x, so q^(N+1)=0. Introduce a second polynomial variable z and set

\[
H(z)=\sum_{k=0}^{N}z^kq^k\prod_{j=k+1}^{N}(1-q^j),
\qquad
G(z)=\prod_{j=1}^{N}(1-zq^j),
\]

\[
P=\prod_{j=1}^{N}(1-q^j).
\]

Direct finite algebra gives

\[
H(qz)=(1-qz)H(z),\qquad
(1-qz)G(qz)=G(z).
\]

The boundary terms vanish because q^(N+1)=0. The factor 1−qz is invertible in A[z], by a finite geometric sum. Hence K(z)=H(z)G(z) satisfies K(qz)=K(z).

For each r>0, comparison of the coefficient of z^r gives

\[
(1-q^r)[z^r]K(z)=0.
\]

Since q^r is nilpotent, 1−q^r is invertible. Every positive-degree coefficient of K is therefore zero. Its constant coefficient is P, giving

\[
H(z)G(z)=P.\tag{2}
\]

At z=1, G(1)=P is invertible, so H(1)=1. Differentiate (2) with respect to z and evaluate at 1. The product rule gives

\[
G'(1)=-P\sum_{i=1}^{N}\frac{q^i}{1-q^i},
\]

and therefore

\[
W_N(q)=H'(1)=\sum_{i=1}^{N}\frac{q^i}{1-q^i}
=\sum_{i=1}^{N}\sum_{j=1}^{N}q^{ij}.
\]

The quotients here are multiplication by inverses of units. Every sum is finite; terms beyond the displayed bounds vanish by nilpotence. This proves (1).

The Lean module `Uchimura.lean` proves the algebra first in any commutative ring with q^(N+1)=0, then specializes using `AdjoinRoot (X^(N+1))`. The theorem `finite_uchimura_coeff` concludes equality of the coefficients of every degree n≤N. No convergence premise, imported Uchimura theorem, or unproved q-binomial identity is used.

### 4. Count divisors to obtain the row sum

Choose N=n≥1 in (1). The coefficient of x^n on its right is the number of ordered pairs (i,j) with

\[
1\le i,j\le n,\qquad ij=n.
\]

Each positive divisor i of n gives exactly one pair (i,n/i), so this coefficient is d(n). The Lean proof supplies a bijection with `Nat.divisorsAntidiagonal` and then with `Nat.divisors`.

Since S_n=W_n and C_k=x^kR_k is the generating polynomial of column k,

\[
\sum_{k=1}^{n}T(n,k)=[x^n]S_n=d(n).
\]

All columns k>n have T(n,k)=0, so this finite sum is exactly the source's sum over all positive columns. This proves Conjecture 1.

### 5. Obtain the diagonal

The recurrence gives R_n(0)=n. Also

\[
R_n=n-S_{n-1},\qquad S_n=S_{n-1}+x^nR_n.
\]

For n≥1, taking the coefficient of x^n in the second identity gives

\[
d(n)=[x^n]S_{n-1}+n.
\]

Taking that coefficient in the first gives

\[
[x^n]R_n=-[x^n]S_{n-1}=n-d(n).
\]

Finally, the already proved column formula yields

\[
T(2n,n)=[x^{2n}]x^nR_n=[x^n]R_n=n-d(n).
\]

This includes n=1, where T(2,1)=0=1−d(1), and proves Conjecture 3.

## Prior work and source status

Mats Granvik introduced A389524 on October 7, 2025. The retrieved official export, revision 19 of October 22, 2025, continues to label these assertions as Conjectures 1 and 3. Its recorded finite checks are not used as proof premises.

The divisor identity used in the proof is classical:

- K. Uchimura, *An identity for the divisor generating function arising from sorting theory*, Journal of Combinatorial Theory, Series A **31** (1981), 131–135. [DOI](https://doi.org/10.1016/0097-3165(81)90009-1).
- D. M. Bressoud and M. V. Subbarao, *On Uchimura's connection between partitions and the number of divisors*, Canadian Mathematical Bulletin **27** (1984), 143–145. [DOI](https://doi.org/10.4153/CMB-1984-022-5).

This package claims the proved connection between A389524's defining recurrence and its two stated targets, together with complete formal verification. It does not claim that Uchimura's identity, divisor-generating series, or the finite-product method is new. Bounded exact-identifier and mathematical-description searches did not locate an earlier proof of these two specific conjectures. That is a search finding, not an assertion of exhaustive historical priority or OEIS editorial acceptance. Details and source revisions are recorded in [source_checks.md](source_checks.md).

## Formal verification

- [Uchimura.lean](Uchimura.lean): finite algebraic proof of the classical identity, its quotient-ring specialization, and the polynomial recurrences.
- [Proof.lean](Proof.lean): literal recursive triangle, column bridge, divisor-count bijection, and the public theorems `A389524.row_sum` and `A389524.diagonal`.
- [verification.txt](verification.txt): fresh build of the exact pinned package and source hashes.
- `AUDIT.md` and `audit-verification.txt`: independent mathematical review and recompilation records, added with the completed audit.
- [sources](sources): official OEIS source snapshots, including the separately unclaimed Conjecture 2 target for clarity of scope.

Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` verify the proof. The printed public theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`. There are no unfinished proofs, custom axioms, `native_decide` calls, or unsafe proof replacements.

## Reproduce

With the pinned toolchain selected, run from this directory:

```sh
lake exe cache get
lake build
```

The manifest pins the transitive dependencies. The two source modules are standalone within this package; they do not import another conjecture package or any local working file.
