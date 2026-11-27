# Gaps and their frequencies in the Wythoff ceiling array

Two conjectures of Clark Kimberling ask which gaps can occur between consecutive positive integers that appear twice or never in the Wythoff ceiling array. Both have exact answers. The omitted list has a single gap of size 2, from 1 to 3. Its other gaps have exactly the same limiting frequencies as the gaps in the doubled list. [Manuscript (PDF)](ceiling-array.pdf) · [LaTeX source](ceiling-array.tex) · [Array definition](https://oeis.org/A341260) · [Doubled conjecture](https://oeis.org/A341261) · [Omitted conjecture](https://oeis.org/A341262)

| Set | Consecutive gap sizes | Natural density |
| --- | --- | --- |
| Integers at exactly two array positions | 3, 5, 10, 13 | $\varphi^{-4}$ |
| Positive integers at no array position | 2, 3, 5, 10, 13 | $\varphi^{-4}$ |

Here $\varphi=(1+\sqrt5)/2$. Among consecutive gaps in either list, the proportions for sizes $3,5,10,13$ are $\varphi^{-2},\varphi^{-3},\varphi^{-4},\varphi^{-3}$, respectively. The manuscript also gives exact counts below each Fibonacci number and an $O(\log^2(N+2))$ counting error for arbitrary endpoints.

## How the proof works

Write a positive integer as a sum of distinct, nonconsecutive Fibonacci numbers, using $F_2=1$. If its two least summands are $F_i,F_j$, put $r=i-2$ and $v=j-i-2$. Its multiplicity is the sum of three indicators, one for odd $r$, one for odd $v$, and one for $r=0$ with even $v$. An integer with just one summand has multiplicity $r\bmod 2$. For example, $10=F_3+F_6$ gives $r=v=1$. Its two entries are in columns 1 and 4.

The two parities and the possibility of a missing summand give ten states for reading a Fibonacci word. Blocks of legal suffixes cover successive integers in order. Keeping the first and last hit of each block proves that no further gap sizes occur. Counting the four gaps across the same joins gives the frequency theorem.

## Formal proof

- [Shift.lean](Shift.lean) and [Codes.lean](Codes.lean) connect the real ceiling formula to a bijection between Fibonacci codes and the nonnegative integers.
- [Columns.lean](Columns.lean) identifies all possible columns of a code and proves row uniqueness in each. [States.lean](States.lean) proves that the state calculation recognizes the two sets.
- [Blocks.lean](Blocks.lean) verifies the finite boundary tables and proves the recurrence for every block width. [Gaps.lean](Gaps.lean) proves `doubled_gaps`, `missing_gaps`, and `unique_gap_two`, including witnesses of every gap.
- [Counts.lean](Counts.lean) proves that the error from a reference Fibonacci number is affine on each parity of the block width. [Frequencies.lean](Frequencies.lean) bounds arbitrary prefixes.
- [ArrayStatistics.lean](ArrayStatistics.lean) states the limiting densities and relative gap frequencies directly for the predicates `Doubled` and `Missing`. It also proves the four formulas in `fibonacci_endpoint_counts`.

## Reproduce the checks

Run these commands in this directory. The Lean toolchain and mathlib revision are pinned.

```sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

The Python check enumerates the defining array using integer square roots, checks the greedy Fibonacci multiplicity formula for every positive input through 250,000, and independently verifies the finite gap and counting certificates. [Verifier](verify.py) · [Build and verification record](verification.txt)
