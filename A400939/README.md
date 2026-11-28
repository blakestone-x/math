# An infinite prime family for the generalized halving Recamán walk

**Status:** a proved infinite family within the generalized-divisor conjecture in [OEIS A400939](https://oeis.org/A400939). This package does **not** settle that conjecture for every divisor that is not a power of two, and it does not settle the original halving walk's positive-integer occurrence conjecture.

For every odd prime $p\equiv2$ or $3\pmod5$, the walk with division by $p$ divides **exactly once**. That division occurs at index $p$ or $p+1$, and every subsequent value has an explicit quadratic formula. The proof starts from the original rule, including its restriction that a division may only produce a previously unseen value.

Both the all-index classification and the infinitude of the proved family are checked in Lean 4.19.0, with mathlib pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The infinitude theorem invokes mathlib's existing proof of Dirichlet's theorem; quadratic reciprocity is also imported from mathlib. Those classical theorems are credited dependencies, not contributions claimed by this package.

## Source problem and exact conventions

The source entry was introduced by Zlatko Damijanic on October 10, 2026. Its generalized-divisor comment asks whether replacing the divisor 2 by any positive integer that is not a power of two makes the resulting walk eventually stop dividing. The source records computational evidence through divisor $10^{10}$; that finite evidence is not used in this proof. The pinned entry is revision 58, dated November 5, 2026, from [the immutable OEIS data export](https://github.com/oeis/oeisdata/blob/df38d77b83a78d8ab5aaa501dec6e3a3db977f01/seq/A400/A400939.seq).

For a fixed positive divisor $k$, define

$$
a_k(1)=1,
\qquad
a_k(n+1)=
\begin{cases}
a_k(n)/k,&k\mid a_k(n)\text{ and }a_k(n)/k\notin\{a_k(1),\ldots,a_k(n)\},\\
a_k(n)+n+1,&\text{otherwise},
\end{cases}
\quad n\ge1.
$$

Only the division branch checks whether its result has already appeared. An addition is allowed to revisit a value. The Lean definition `walk` implements precisely this rule. Its auxiliary value at index zero is excluded from every visited-value test; the mathematical sequence remains one-based. The theorem `walk_followsRule` proves the correspondence between the recursive definition and the displayed rule.

Let $T_n=n(n+1)/2$, with $T_0=0$. In the formal proof, `triangle` is defined by $T_{n+1}=T_n+n+1$, and `two_mul_triangle` proves the usual closed formula.

## The theorem

**Theorem.** Let $p$ be an odd prime, and suppose that 5 is not a square modulo $p$. Set $q=(p-1)/2$. Exactly one division takes place in $a_p$, with the following alternatives.

1. If $q$ is not a positive triangular number, the division occurs at $d=p$. Then
   $$
   a_p(n)=T_n\quad(1\le n<p),
   \qquad
   a_p(n)=\frac{n(n+1)-p^2-1}{2}\quad(n\ge p).
   $$

2. If $q$ is a positive triangular number, the division occurs at $d=p+1$. Then
   $$
   a_p(n)=T_n\quad(1\le n\le p),
   \qquad
   a_p(n)=\frac{n(n+1)-(p+1)^2}{2}\quad(n\ge p+1).
   $$

In either alternative, $p\nmid a_p(n)$ for every $n\ge d$, and consequently every later transition uses addition.

For an odd prime, quadratic reciprocity makes the hypothesis equivalent to

$$
p\equiv2\text{ or }3\pmod5.
$$

The formal main theorem `walk_prime_residue_classes` states the two possible indices and doubled offsets, the entire triangular prefix, the unique division, the exact tail identity, and nondivisibility throughout that tail. `division_at_prime_iff` gives the finite triangular test distinguishing the alternatives. In that theorem the triangular witness is explicitly restricted to $1\le i<p$; this is equivalent to the unrestricted positive-triangular test, since $T_i\ge i$ and $q<p$.

### Examples

These are instances of the theorem, not evidence replacing its universal proof.

| Divisor $p$ | $(p-1)/2$ | Unique division index $d$ | Value at the division | Formula for all $n\ge d$ |
|---:|---:|---:|---:|---|
| 3 | $1=T_1$ | 4 | 2 | $T_n-8$ |
| 7 | $3=T_2$ | 8 | 4 | $T_n-32$ |
| 13 | $6=T_3$ | 14 | 7 | $T_n-98$ |
| 17 | 8 | 17 | 8 | $T_n-145$ |
| 23 | 11 | 23 | 11 | $T_n-265$ |
| 43 | $21=T_6$ | 44 | 22 | $T_n-968$ |

For example, with divisor 7 the walk starts

$$
1,3,6,10,15,21,28,4,13,23,34,46,\ldots.
$$

The attempted division of 21 would produce the previously visited 3, so the walk adds 7 and reaches 28. The next division produces the new value 4. The theorem then proves $a_7(n)=T_n-32$ for every $n\ge8$.

## Proof

### 1. The prefix is triangular

Consider a prime divisor $p$. If $1\le n$ and $n+1<p$, then $p\nmid T_n$: otherwise $p\mid2T_n=n(n+1)$, so primality would force $p\mid n$ or $p\mid n+1$, although both are positive and smaller than $p$.

Starting at $a_p(1)=T_1=1$, induction therefore gives

$$
a_p(n)=T_n\qquad(1\le n<p).
$$

This establishes the prefix directly from the source transition rule; no experimentally inferred recurrence is substituted for that rule.

### 2. The first division is at $p$ or $p+1$

Write $q=(p-1)/2$. The value just before index $p$ is

$$
a_p(p-1)=T_{p-1}=pq.
$$

If $q$ has not appeared in the triangular prefix, the rule divides and gives $a_p(p)=q$. Thus

$$
2a_p(p)+p^2+1=p(p+1).
$$

Otherwise $q=T_j$ for some positive $j<p$. The attempted quotient is already visited, so the rule adds $p$, yielding $a_p(p)=T_p$. At the following step the proposed quotient is

$$
T_p/p=(p+1)/2=q+1.
$$

Two positive triangular numbers cannot differ by one: if $T_j<T_i$, then $i\ge j+1$ and

$$
T_i-T_j\ge T_{j+1}-T_j=j+1\ge2.
$$

Consequently $q+1$ is absent from the entire triangular prefix through index $p$. The next division is therefore taken, and

$$
a_p(p+1)=(p+1)/2,
\qquad
2a_p(p+1)+(p+1)^2=(p+1)(p+2).
$$

This part of the proof holds for every odd prime, without the quadratic-nonresidue hypothesis.

### 3. A modular obstruction makes the tail permanent

In the first case put $D=p^2+1$, and in the second put $D=(p+1)^2$. At the first division index $d$, we have established

$$
2a_p(d)+D=d(d+1),
\qquad D\equiv1\pmod p.
$$

Suppose that for some $n\ge d$,

$$
2a_p(n)+D=n(n+1).
$$

If $p\mid a_p(n)$, reduction modulo $p$ gives $n(n+1)\equiv1\pmod p$. Hence

$$
(2n+1)^2=4n(n+1)+1\equiv5\pmod p,
$$

contradicting the hypothesis that 5 is not a square. Thus the division branch is impossible. The rule adds $n+1$, and

$$
2a_p(n+1)+D
=2a_p(n)+D+2(n+1)
=(n+1)(n+2).
$$

Induction proves both the tail identity and nondivisibility at every later index. No visited-value assumption is needed in this final step because divisibility itself is impossible.

There was no division before $d$, there is a division at $d$, and the tail contains no divisible value. This proves that the division is unique.

### 4. An infinite family follows

Since $5\equiv1\pmod4$, quadratic reciprocity says that 5 is a square modulo an odd prime $p$ exactly when $p$ is a square modulo 5. The squares modulo 5 are 0, 1, and 4. Thus primes in the two classes 2 and 3 satisfy the required nonresidue condition, with the even prime 2 excluded.

Dirichlet's theorem supplies arbitrarily large primes $p\equiv3\pmod5$. Applying the classification to those primes proves that the set of divisors covered here is infinite. The Lean declaration `arbitrarily_large_single_division` checks this consequence: for every bound $N$, it produces a prime $p>N$ in class 3, an index $d\in\{p,p+1\}$ that is the only division index, and addition at every transition after index $p+1$.

## Formal verification

`Proof.lean` contains the literal walk, the source-rule bridge, the arithmetic lemmas, the initial dynamics, the permanent-tail argument, the residue-class specialization, and the infinitude theorem. Its principal declarations are:

| Declaration | Content |
|---|---|
| `walk_followsRule` | The recursive walk satisfies the original visited-value rule. |
| `first_prime_division` | For every odd prime, the first division occurs at $p$ or $p+1$, with the stated offset. |
| `division_at_prime_iff` | The finite triangular-prefix test selects the first index. |
| `permanent_translate` | The quadratic nonresidue obstructs every later division. |
| `walk_prime_residue_classes` | Complete all-index classification for primes $p\ne2$ in classes 2 or 3 modulo 5. |
| `arbitrarily_large_single_division` | The classified prime family is infinite, via mathlib's Dirichlet theorem. |

Both principal end theorems report only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` placeholders, admitted lemmas, additional axioms, unsafe declarations, or `native_decide` calls. `decide` is used only for small finite facts such as the square table modulo 5 and primality of 5.

To reproduce the project in an ordinary environment with the pinned toolchain and network access:

```sh
lake exe cache get
lake build
lake env lean Proof.lean
```

The submitted verification transcript records the separate local compilation against the same pinned dependency cache. See `verification.txt`, `AUDIT.md`, `source_checks.md`, and `SHA256SUMS.txt` for the build, independent review, bounded source-status check, and file fingerprints.

## Scope and provenance

The mathematical contribution here is the exact initial-division and permanent-tail classification for the specified prime family. The underlying conjecture, its finite computational evidence, quadratic reciprocity, and Dirichlet's theorem are existing work. Bounded searches of both search engines, the current trureturing results catalog, and trureturing GitHub issues found no previous proof of this particular classification. That is a documented search result, not a guarantee of worldwide novelty.

This package leaves the generalized stopping conjecture unresolved outside the proved family. In particular, this work makes no stopping claim for arbitrary composite divisors or for the remaining odd-prime residue classes, and no occurrence claim for the original divisor-2 walk.

### References

1. Zlatko Damijanic, [OEIS A400939](https://oeis.org/A400939), introduced October 10, 2026; [pinned export](https://github.com/oeis/oeisdata/blob/df38d77b83a78d8ab5aaa501dec6e3a3db977f01/seq/A400/A400939.seq). The exact source snapshot is retained in `sources/A400939.seq`.
2. Eric W. Weisstein, [Halving Recamán Sequence](https://mathworld.wolfram.com/HalvingRecamanSequence.html), MathWorld. Used to cross-check the original divisor-2 rule.
3. The mathlib contributors, [quadratic reciprocity](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean), in particular `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`.
4. The mathlib contributors, [Dirichlet's theorem on primes in arithmetic progressions](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/LSeries/PrimesInAP.lean), in particular `Nat.forall_exists_prime_gt_and_eq_mod`.
