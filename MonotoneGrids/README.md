# Exact counts for seven families of binary grids

These Lean proofs establish Colin Barker's two conjectures in each of seven
OEIS entries for binary grids enumerated by R. H. Hardin. Six entries ask
for a generating function and a recurrence. A208138 asks for a generating
function and a factored closed form. The proofs also recover the polynomial
marked empirical in each entry.

Here $n$ is the positive height. The two horizontal triples vary by entry.
All seven forbid 001 and 101 vertically, read down a column.

| OEIS source | Width | Forbidden horizontally | Exact count $a(n)$ | Lean proof |
|---|---:|---|---|---|
| [A207065](https://oeis.org/A207065) | 5 | 001, 010 | $(7n^5+210n^4+315n^3-112n)/30$ | [A207065.lean](A207065.lean) |
| [A207167](https://oeis.org/A207167) | 6 | 000, 101 | $(19n^4+190n^3-57n^2-76n)/4$ | [A207167.lean](A207167.lean) |
| [A207449](https://oeis.org/A207449) | 4 | 000, 001 | $10n^3+10n^2-10n$ | [A207449.lean](A207449.lean) |
| [A207452](https://oeis.org/A207452) | 7 | 000, 001 | $168n^4-84n^3-84n^2+42n$ | [A207452.lean](A207452.lean) |
| [A207598](https://oeis.org/A207598) | 7 | 000, 010 | $120n^4+40n^3-200n^2+80n$ | [A207598.lean](A207598.lean) |
| [A208138](https://oeis.org/A208138) | 4 | 001, 011 | $9n^2(n+1)^2/4$ | [A208138.lean](A208138.lean) |
| [A209648](https://oeis.org/A209648) | 6 | 001, 100 | $(66n^4+88n^3-66n^2-22n)/3$ | [A209648.lean](A209648.lean) |

## The counting argument

Let $R$ be the set of width-$w$ rows satisfying the two horizontal
restrictions. Treat each row as the set of columns containing a 1. The
forbidden vertical triples exhaust both possibilities for the bit above
a 0 followed by a 1. Consequently row two may be arbitrary, and every
row after it must be a subset of the row immediately above it.

For a legal row $r$, let $F_r(h)$ count the length-$h$ suffixes allowed
below $r$ under this subset rule. Choosing the next row gives

$$
F_r(0)=1,\qquad F_r(h+1)=\sum_{s\in R,\ s\subseteq r}F_s(h).
$$

The all-ones row $t$ is legal in each of the seven cases. It allows every
legal second row. With $|R|$ independent choices for row one, the grid
count is $a(n)=|R|F_t(n-1)$, including height one.

For each legal $r$ the certificate gives an integer polynomial $P_r$ of
degree at most five. Lean checks its constant term is 120 and checks
all six coefficients in the identity

$$
P_r(x+1)=\sum_{s\in R,\ s\subseteq r}P_s(x).
$$

Induction now gives $120F_r(h)=P_r(h)$ for every $h$. The factor
$120=5!$ clears denominators. To reconstruct the candidate polynomials,
compute the six suffix counts at $h=0,\ldots,5$ by the displayed
recurrence and interpolate $120F_r$. The coefficient identities above
certify each interpolation for all heights. The certificate lists have
5 to 12 distinct polynomials, shared by rows with identical suffix counts.

For the generating functions set $a(0)=0$, as required by the offset in
each OEIS entry. Multiplying a formal series by $1-x$ takes its backward
difference with zero padding. For each grid family Lean applies this
operation until the coefficients vanish, verifies the remaining numerator
coefficients, and proves the identity in the integer formal power series
ring. The denominator has constant term one. Taking the coefficients above
the numerator yields the recurrences with the indexed bounds in the
source entries. For A208138 the polynomial also factors as nine times the
square of the $n$th triangular number.

## Verification and submission files

- [Boards.lean](Boards.lean) constructs the grids as lists of rows.
- [Semantics.lean](Semantics.lean) proves that list membership is
  equivalent to satisfying the literal pattern rules at the required
  height. It also proves that the enumeration has no duplicates.
- [Certificate.lean](Certificate.lean) proves the suffix-count induction
  and the finite-difference identity for formal power series.
- In each entry's file, `closed_form` proves the tabulated polynomial and
  `main` states the two conjectures from OEIS. Both print their axiom dependencies.

The project pins Lean 4.33.1 and mathlib. Run from this directory with an
elan-managed Lean installation.

```sh
lake exe cache get Mathlib.Data.List.Nodup Mathlib.Tactic.Ring Mathlib.Tactic.LinearCombination Mathlib.RingTheory.PowerSeries.Basic
lake build
```

For the Left to Solve submission layout, the export script emits one
statement and one proof. The statement contains the review placeholder
required by the site. The separate proof imports the statement module and
establishes its type independently. For example,

```sh
python3 export.py A207449 /tmp/grid-submission
```

A separate check compared each polynomial and rational generating
function with the 210 terms in its linked OEIS entry's b-file, for
1,470 checked terms across the seven sequences.
