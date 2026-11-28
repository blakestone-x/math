# A cubic formula for four-column binary grids

R. H. Hardin's OEIS sequence [A207020](https://oeis.org/A207020) counts
binary grids of height $n$ and width four. Horizontal triples are read left
to right and must avoid 000 and 011. Vertical triples are read top to bottom
and must avoid 001 and 101. The sequence starts at height one.

For every $n\ge1$, its count is

$$
a(n)=\frac{3n(4n^2+9n-7)}2.
$$

This proves the cubic recorded as empirical in OEIS and both claims
conjectured there by Colin Barker in 2018. The generating function is

$$
\sum_{n\ge1}a(n)x^n=\frac{9x(1+5x-2x^2)}{(1-x)^4},
$$

and $a(n)=4a(n-1)-6a(n-2)+4a(n-3)-a(n-4)$ for $n>4$.

## Proof

The forbidden vertical triples are exactly those ending in 01. Thus a
column may change freely from row one to row two. From row two onward,
each row's 1-bits form a subset of the preceding row's 1-bits.

Number the columns 0 through 3 from the left and give column $j$ weight
$2^j$. Of the sixteen row masks, precisely nine pass both horizontal
triple tests. They fall into four classes. In the last column, each letter
stands for one possible next row. For example, a mask of type $W$ has two
possible successors of type $U$, two of type $V$, and one of type $W$.

| Type | Row masks | Types of allowed successors |
|---|---|---|
| $U$ | 2, 4, 9 | $U$ |
| $V$ | 3, 5, 10 | $U,V$ |
| $W$ | 7, 11 | $U,U,V,V,W$ |
| $Z$ | 15 | $U,U,U,V,V,V,W,W,Z$ |

Let $U_k,V_k,W_k,Z_k$ count the legal suffixes of length $k$ below a
row of each type, under the subset rule. Each starts at one for the
empty suffix. The table gives the four simultaneous recurrences

$$
\begin{aligned}
U_{k+1}&=U_k,\\
V_{k+1}&=U_k+V_k,\\
W_{k+1}&=2U_k+2V_k+W_k,\\
Z_{k+1}&=3U_k+3V_k+2W_k+Z_k.
\end{aligned}
$$

Substitution and induction give $U_k=1$, $V_k=k+1$,
$W_k=k^2+3k+1$, and $6Z_k=4k^3+21k^2+23k+6$.
There are nine choices for row one. For the remaining $n-1$ rows,
starting the subset rule below the all-ones mask allows every choice of
row two. Hence $a(n)=9Z_{n-1}$, including $n=1$. Expanding gives the
claimed cubic.

Set $a(0)=0$ for the generating series. The fourth finite difference of
the cubic vanishes, yielding the recurrence. Multiplication by $(1-x)^4$
takes precisely this difference in degrees four and higher. The first
four coefficients of the product are $0,9,45,-18$, which give the stated
numerator.

## Lean verification

The project pins Lean 4.33.1 and the mathlib revision in the Lake manifest.
From this directory run

```sh
lake exe cache get Mathlib.Data.List.Nodup Mathlib.Tactic.Ring Mathlib.Tactic.LinearCombination Mathlib.RingTheory.PowerSeries.Basic
lake build
```

- [Grid.lean](Grid.lean) enumerates actual lists of rows.
- [Enumeration.lean](Enumeration.lean) independently specifies the four
  forbidden triples. Its two theorems prove that membership in the
  enumeration is equivalent to having the required height and satisfying
  the rules, and that no grid is counted twice.
- [Proof.lean](Proof.lean) proves the cubic, the coefficient identity, and the recurrence.
- [Series.lean](Series.lean) proves the identity in the formal power series
  ring over the integers, with the denominator cleared, and packages both
  of Barker's conjectures in theorem `OMA.S_oeis_a207020.main`.

The build prints the axiom dependencies of the main results. They are
within Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
As a separate numerical check, the cubic agrees with all 210 values in
[Hardin's OEIS table](https://oeis.org/A207020/b207020.txt).
