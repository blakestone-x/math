# A289004: a false length recurrence and its structural obstruction

The replacement-length conjecture recorded in [A289004](https://oeis.org/A289004)
is false. It also fails for the two other rules that refer to the same length
sequence, [A289035](https://oeis.org/A289035) and
[A289239](https://oeis.org/A289239).

All three literal scanners have the **same actual length sequence**. They agree
with A289004 through iteration 21, but at iteration 22 their length is
**268184**, whereas A289004 is **268182**. More strongly, their lengths cannot
satisfy any eventual constant-coefficient recurrence of the form

$$
L_{n+d}=c_{d-1}L_{n+d-1}+\cdots+c_0L_n,
\qquad c_i\in\mathbb Z.
$$

The proof includes the literal scanning definition, the common count equations,
the first failure, a corrected recurrence with rounding, and the obstruction
for every order and every finite initial exception set. The formal statements
are in [Proof.lean](Proof.lean) and [NoRecurrence.lean](NoRecurrence.lean).

## Exact source rules and indexing

Every source begins with $w_0=00$. The scanner reads the input from left to
right, consumes each matched pair once, and appends its replacement without
rescanning it during that pass. An unmatched letter is copied. A final
singleton is retained; A289035 states this convention explicitly.

| Source word | Image of `00` | Image of `01` | Image of `10` | Lean variant |
| --- | --- | --- | --- | --- |
| [A289001](https://oeis.org/A289001) | `0010` | `001` | `010` | `Variant.left` |
| [A289035](https://oeis.org/A289035) | `0010` | `010` | `010` | `Variant.middle` |
| [A289239](https://oeis.org/A289239) | `0010` | `100` | `010` | `Variant.right` |

The scanner contains the unmatched `11` branch as well. The proof establishes
that every source iterate has no adjacent ones and ends in zero, so this
branch is never reached in these iterates. These properties are proved from
the literal rules, not imposed as hypotheses on the source words.

A289004 defines its scalar sequence independently by

$$
a_n=2a_{n-1}-a_{n-2}+2a_{n-4}-a_{n-5}
       +a_{n-7}-a_{n-8}-a_{n-10}\qquad(n\ge10),
$$

with initial values

$$
(a_0,\ldots,a_9)=(2,4,7,11,18,31,52,89,151,257).
$$

Its prose prints index 9 twice. The displayed terms and Mathematica program
unambiguously place 151 at index 8 and 257 at index 9; the formal independent
definition `reference` uses those values. The counterexample occurs far beyond
that typographical issue.

There are three distinct mapping assertions in this family. The statement in
A289004 and its repetition in A289001 are the same assertion and are counted
once. The structural theorem below handles all three mappings uniformly.

## Proof of the corrected count dynamics

Let $L_n=|w_n|$, let $O_n$ be the number of ones in $w_n$, and put
$e_n=L_n\bmod2$. Because there are no `11` pairs and the final letter is zero,
the scanner consumes exactly $\lfloor L_n/2\rfloor$ pairs and, when $L_n$ is
odd, leaves one final zero.

Each consumed pair produces exactly one 1. A `00` pair produces four letters;
a mixed pair produces three. Every input 1 belongs to a mixed pair. Therefore

$$
\boxed{
 O_{n+1}=\left\lfloor\frac{L_n}{2}\right\rfloor,
 \qquad L_{n+1}=2L_n-O_n-e_n.
}
$$

The initial state is $(L_0,O_0)=(2,0)$ for all three rules. These equations
prove that their lengths and numbers of ones agree at every iteration, even
though their finite words differ. Eliminating $O_n$ gives the corrected scalar
recurrence

$$
\boxed{
L_{n+2}+\left\lfloor\frac{L_n}{2}\right\rfloor
       +(L_{n+1}\bmod2)=2L_{n+1},
\qquad L_0=2,\quad L_1=4.
}
$$

The formal theorem `word_counts` connects this arithmetic state to the actual
lists produced by every literal scanner. `first_failure` then proves both
agreement at all indices $n<22$ and the inequality at $n=22$ through this
proved bridge. The kernel does not rely on an unverified simulation of a long
word.

| Iteration $n$ | Actual $L_n$ for all three rules | A289004 $a_n$ |
| ---: | ---: | ---: |
| 19 | 53908 | 53908 |
| 20 | 92027 | 92027 |
| 21 | 157099 | 157099 |
| **22** | **268184** | **268182** |
| 23 | 457819 | 457812 |

## A uniform error bound and the true growth ratio

Set

$$
\mu=1-\frac{\sqrt2}{2},\qquad
\lambda=1+\frac{\sqrt2}{2},\qquad
S_n=L_n-(2+\sqrt2)O_n.
$$

Substitution of the exact count equations gives

$$
S_{n+1}=\mu S_n+(1-\mu)e_n.
$$

Here $S_0=2$, $0<\mu<1$, and $e_n\in\{0,1\}$. Induction proves
$0\le S_n\le2$ for every $n$. Also each good word has at most half its letters
equal to 1, and the count equations yield

$$
L_{n+1}\ge L_n+\left\lfloor\frac{L_n}{2}\right\rfloor,
\qquad L_n\ge n+2.
$$

In particular $L_n\to\infty$. The identity

$$
\frac{L_{n+1}}{L_n}
=\lambda+\mu\frac{S_n}{L_n}-\frac{e_n}{L_n}
$$

now proves, with existence of the limit included,

$$
\boxed{\lim_{n\to\infty}\frac{L_{n+1}}{L_n}
=1+\frac{\sqrt2}{2}.}
$$

For every fixed $j$, multiplication of the successive ratios consequently
gives $L_{n+j}/L_n\to\lambda^j$.

## Why no eventual monic integer recurrence can work

Suppose a monic polynomial $p(X)=\sum_i p_iX^i\in\mathbb Z[X]$ gave an eventual
relation $\sum_i p_iL_{n+i}=0$. Divide by $L_n$ and use the fixed-shift limits.
The result is $p(\lambda)=0$, so $\lambda$ would be an algebraic integer.

But

$$
(\lambda-1)^2=\frac12.
$$

Algebraic integers are closed under subtraction and multiplication. Thus
$1/2$ would be a rational algebraic integer, hence an integer, a contradiction.

`literal_no_eventual_monic_relation` states the full obstruction directly on
the literal source words: for every monic $p\in\mathbb Z[X]$ and every cutoff
$N$, there is an $n\ge N$ for which its length relation is nonzero.
`original_recurrence_fails_after_every_cutoff` specializes it to the exact
order-ten polynomial printed in A289004. The result concerns monic integer
recurrences; no broader coefficient scope is asserted here.

## Prior work and scope

Dekking and Keane proved that the infinite fixed word A289001 is the Pell
word in [*Two-block substitutions and morphic words*](https://arxiv.org/abs/2202.13548),
Theorem 4. The OEIS also records Dekking's related density argument in
[A289037](https://oeis.org/A289037), and his floor recurrence for the
**final-letter-removed** version in [A293077](https://oeis.org/A293077).
Those are prior results and are not counted as new results of this package.
The retained-singleton lengths here differ from A293077 already at iteration 2:
they are 7 rather than 6.

The current primary entries still contain the retained-singleton A289004
length conjectures. The bounded prior-work search included both web engines,
the current trureturing catalogue, the primary paper, the user's existing
repository, global GitHub code search, and separate exact and semantic
searches in `VladimirReshetnikov/ProveIt`. No matching earlier refutation was
identified in those checks. This is not an unconditional claim of priority.
Exact snapshots, hashes, search scope, and limitations are recorded in
[source_checks.md](source_checks.md).

## Formal verification

The package is pinned to **Lean 4.19.0** and mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
lake exe cache get
lake build
sha256sum -c SHA256SUMS.txt
```

All seven local modules are included in the default Lake target. The proof
uses no admitted statements, extra axioms, or native-decision shortcuts.
The export module prints the axioms of the main endpoints. The
[fresh author build](verification.txt) and [fresh independent build](independent_build.log)
both passed with only the standard Lean axioms. The separate
[independent review](independent_review.md) found no mathematical or source-alignment
issues and independently matched all six source exports.

| File | Checked content |
| --- | --- |
| [Scanner.lean](Scanner.lean) | Literal scanner, preservation of the valid-word invariant, exact one-pass length and ones counts |
| [Counts.lean](Counts.lean) | Common arithmetic state, all-index source bridge, corrected rounding recurrence, growth lower bound |
| [Counterexample.lean](Counterexample.lean) | Independent A289004 recurrence, all earlier agreement, first failure at iteration 22 |
| [NonIntegral.lean](NonIntegral.lean) | The growth constant is not an algebraic integer |
| [Growth.lean](Growth.lean) | Uniform discrepancy bound and actual consecutive/fixed-shift length-ratio limits |
| [NoRecurrence.lean](NoRecurrence.lean) | Every monic integer recurrence fails after every cutoff |
| [Proof.lean](Proof.lean) | Source-facing refutations, corrected recurrence, ratio limit, exact order-ten specialization, axiom audit |

The independent diagnostic program [verify.py](verify.py) directly scans finite
words and compares them with the proved count equations. It is a reproducible
check; the universal mathematical claims are established by Lean.
