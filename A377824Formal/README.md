# A377824: a formal companion for minimum-part positions

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 26, 2026

## Final-publication addendum — November 26, 2026 (America/Chicago)

This Lean development was completed independently during the same work
period as the repository's [A377824 manuscript](../A377824/README.md).
The final repository check found that manuscript already present in
`blakestone-x/math` at commit
`c92ab48c98acba51cb42ceb73536a7bad251ec2d`, before publication of this
formal package. It proves the same exact main term and the stronger
error estimate $O(n^2\varphi^n)$, where $\varphi=(1+\sqrt5)/2$, using
the minimum-one generating function and a Fibonacci bound.

Accordingly, **A377824Formal is a formal companion and contributes no
additional conjecture resolution to Batch 7**. It supplies a complete
Lean proof of the source asymptotic, the exact polynomial main term,
and the explicit $(7/4)^n$ error bound stated below. The manuscript's
stronger $\varphi^n$ rate is not asserted as a theorem of this package.

The concurrent [README](sources/prior_repo_README.md) and
[LaTeX manuscript](sources/prior_repo_minimum-positions.tex) are preserved
byte-for-byte from that commit. Their Git blob identifiers and SHA-256
hashes appear in [source_checks.md](source_checks.md). The frozen Lean
source, pinned build files, source export, and original verification logs
are unchanged; the directory was renamed from `A377824` to `A377824Formal`.

## Result

For a composition $c=(c_1,\ldots,c_\ell)$ of $n$ into positive integers, put

$$s(c)=\sum_{\substack{1\le j\le\ell\\c_j=\min(c)}}j.$$

Let $a(n)$ be the sum of $s(c)$ over all compositions of $n$, with $a(0)=0$.
This is the defining statistic of [OEIS A377824](https://oeis.org/A377824).
Václav Kotěšovec's April 19, 2025 conjecture is

$$\boxed{a(n)\sim n^2 2^{n-5}.}$$

We prove this on its full asymptotic domain. More precisely, for every
$n\ge2$,

$$\boxed{
0\le a(n)-\frac{(n+1)(n+6)2^n}{32}
\le n^2\left(\frac74\right)^n.
}$$

Equivalently,

$$\frac{a(n)}{n^2 2^{n-5}}
=1+\frac7n+\frac6{n^2}+\varepsilon_n,
\qquad
0\le\varepsilon_n\le32\left(\frac78\right)^n.
$$

Thus the formal proof supplies two explicit correction terms and an
exponentially decaying remaining relative error. This package contributes
one formalization to Batch 7; neither the source asymptotic nor its
correction terms are counted as an additional conjecture resolution here.

## Proof

### 1. Enumerating the actual compositions

Every nonempty composition $c=(c_1,c_2,\ldots,c_\ell)$ has two children:

$$L(c)=(1,c_1,c_2,\ldots,c_\ell),\qquad
R(c)=(c_1+1,c_2,\ldots,c_\ell).$$

Starting from the single composition $(1)$ of $1$, these operations
enumerate the compositions of each succeeding integer exactly once.
A composition whose first part is $1$ has a unique predecessor by
deleting that part; one whose first part is at least $2$ has a unique
predecessor by decreasing that part. The two cases are disjoint.

Consequently the number $C_n$ of compositions is $2^{n-1}$ for $n\ge1$.
For $n\ge2$, the number $H_n$ that begin with a $1$ is $C_{n-1}=2^{n-2}$.
The Lean proof establishes both exhaustion and absence of duplicates,
and proves that its position statistic is literally the sum of the
one-based indices satisfying the minimum condition.

### 2. The exact contribution from parts equal to one

For a composition $c$, let $o(c)$ count its parts equal to $1$, and let
$w(c)$ sum their one-based positions. Write $O_n$ and $W_n$ for their
totals over all compositions of $n$.

If $\alpha(c)$ is $1$ when the first part is $1$ and $0$ otherwise, the
two operations give

| Statistic | $L(c)$ | $R(c)$ |
|---|---|---|
| Number of ones | $o(c)+1$ | $o(c)-\alpha(c)$ |
| Sum of positions of ones | $w(c)+o(c)+1$ | $w(c)-\alpha(c)$ |

In the left child, every old part moves one position to the right. In
the right child, only a possible first $1$ ceases to be a $1$.
Summing the table gives, for $n\ge2$,

$$O_{n+1}=2O_n+C_n-H_n=2O_n+2^{n-2},$$

$$W_{n+1}=2W_n+O_n+C_n-H_n
         =2W_n+O_n+2^{n-2}.$$

The two compositions of $2$ are $(1,1)$ and $(2)$, so $O_2=2$ and
$W_2=3$. Induction now yields

$$O_n=(n+2)2^{n-3},\qquad
\boxed{W_n=\frac{(n+1)(n+6)2^n}{32}}\quad(n\ge2).$$

For example, substituting the first formula into the second recurrence
gives $W_{n+1}=2W_n+(n+4)2^{n-3}$, which the displayed quadratic
expression satisfies. The formal proof uses the equivalent integer
identities $8O_n=(n+2)2^n$ and $32W_n=(n+1)(n+6)2^n$.

### 3. Bounding every composition with minimum larger than one

Let $F_n$ count compositions of $n$ with no part equal to $1$, including
the empty composition at $n=0$. Then $F_0=1$ and $F_1=0$.

For completeness, the same two operations establish the recurrence.
Let $D_n$ count compositions of $n$ whose tail has no $1$. For $n\ge1$,
the left children never contribute to $F_{n+1}$, while a right child
has no $1$ precisely when its predecessor's tail has no $1$. Therefore
$F_{n+1}=D_n$. For the tail statistic, a left child contributes precisely
when its predecessor has no $1$, and a right child has the same tail as
its predecessor. Hence $D_{n+1}=F_n+D_n$. Together with $F_2=1$, this gives

$$F_{n+2}=F_{n+1}+F_n\qquad(n\ge0).$$

Set $q=7/4$. Since $q^2\ge q+1$, induction on this recurrence gives
$F_n\le q^n$ for every $n\ge0$.

If a composition contains a $1$, its minimum parts are exactly its ones,
so $s(c)=w(c)$. If it contains no $1$, its contribution to $W_n$ is zero,
and

$$0\le s(c)\le1+2+\cdots+\ell\le\ell^2\le n^2,$$

because all parts are positive. Summing over the exceptional compositions
therefore gives

$$0\le a(n)-W_n\le n^2F_n\le n^2q^n.$$

Substitute the exact expression for $W_n$ to obtain the claimed bound.
After division by $n^2 2^n/32$, the remainder lies between $0$ and
$32(7/8)^n$. The two rational correction terms and this geometric term
tend to zero, proving the conjecture. ∎

## Formal verification

`Proof.lean` defines compositions as lists of positive natural numbers
and sums the actual minimum-position statistic over their exhaustive
enumeration. Its main checked declarations are:

| Declaration | Content |
|---|---|
| `mem_compositions` | A list appears exactly when all its parts are positive and their sum is the specified integer. |
| `compositions_nodup` | Every such list appears once. |
| `weights_positions`, `a_positions` | The recursive statistic equals the literal sum of one-based minimum positions. |
| `oneWeights_total_formula` | The exact integer form of the polynomial main term. |
| `clean_fibonacci_recurrence`, `clean_bound` | The recurrence and exponential bound for compositions with no ones. |
| `closed_form_error` | The displayed bound for every $n\ge2$. |
| `normalized_bounds`, `normalized_limit` | Explicit bounds on the relative error and convergence to one. |
| `original_conjecture` | Asymptotic equivalence to the exact OEIS expression $n^2 2^{n-5}$. |

No generating-function identity or asymptotic premise is assumed. The
public axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`; the source has no unfinished proofs, added axioms, or
`native_decide` calls.

## Related work and contribution scope

Arnold Knopfmacher and Augustine O. Munagi's
[*Smallest Parts in Compositions*](https://doi.org/10.1007/978-3-642-30979-3_11),
in *Advances in Combinatorics* (2013), pp. 197–207, studies the number
and sum of minimum parts, refined counts by length, and the position of
the **first** minimum part. Their work develops the classical principle
that compositions with minimum one supply the dominant contribution.
Their refined counts also give related positional formulas by symmetry.
This package credits that background and applies an elementary direct
enumeration to the sum of **all** minimum positions in A377824.

The repository's [A238342 result](https://github.com/blakestone-x/math/tree/main/A238342)
concerns a fixed number of occurrences of the minimum. Its asymptotic
has a different exponential base and is a distinct statistic.

The preserved OEIS export, revision 28 of April 19, 2025, still labels
the selected asymptotic a conjecture. The initial bounded exact-statement
and semantic searches did not locate an earlier exact resolution. The
final repository check subsequently found the concurrent A377824
manuscript described in the addendum above, which determines this
package's formal-companion status. The search stages and their limits
are recorded in `source_checks.md`; no claim of exhaustive historical
priority or OEIS editorial acceptance is made.

## Reproduce

With Elan selecting the pinned toolchain, run from this directory:

```sh
lake exe cache get
lake build
```

The package pins Lean 4.19.0 and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The manifest fixes the
transitive dependencies. `verification.txt` records the fresh package
build. `AUDIT.md` and `audit-verification.txt` accompany the independent
review, and `SHA256SUMS.txt` identifies the exact delivered artifacts.
