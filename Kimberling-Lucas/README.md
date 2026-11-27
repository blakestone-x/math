# Kimberling’s prefix conjecture and the Lucas–Wythoff arrays

Blake Stone · Proof developed with OpenAI Codex

Clark Kimberling asked whether the Zeckendorf representations of the integers from 1 through $N$ always contain at least as many terms in total as their greedy Lucas representations. The answer is yes. The paper also answers his question about the column where each Lucas–Wythoff row first contains an adjacent pair from the ordinary Wythoff array. [Manuscript (PDF)](lucas-representations.pdf) · [LaTeX source](lucas-representations.tex) · [Kimberling’s 2020 paper](https://cs.uwaterloo.ca/journals/JIS/VOL23/Kimberling/kimber12.html)

## Exactly when the totals agree

The first ten equality indices are 1, 2, 3, 5, 6, 8, 9, 10, 16 and 17. Every later one has the following form, where $L_h$ is the Lucas number of index $h$.

| Index | Equality positions |
| --- | --- |
| Even $h\ge8$ | $L_h-1, L_h-2$ |
| Odd $h\ge7$ | $L_h-1,L_h-2,L_h-3,L_h-5$ |

A recursion on the changes in Zeckendorf weight when adding a Fibonacci number gives the inequality on every prefix and all its zeros. [A214979](https://oeis.org/A214979) · [A214980](https://oeis.org/A214980) · [Inclusive conjecture and equality classification in Lean](Equality.lean)

## Entry into an ordinary Wythoff row

Write $t=\{n\varphi\}$ for row $n$. In the second Lucas–Wythoff array, the first pair starts the permanent common tail. Its starting column is 3 if $t>1/\sqrt5$ and 5 otherwise. In the first array, these permanent starts shift to columns 4 and 6. There can also be an earlier, isolated pair. For example, the second row contains $(6,10)$ in column 2 and begins its permanent Wythoff tail at $(40,65)$ in column 6. The manuscript gives the two early-column tests. [Row calculation in Lean](RowEntry.lean)

## The mixed Fibonacci–Lucas basis

The joint generating function in Section 3 counts both the Zeckendorf weight and the mixed greedy weight. It gives a nondegenerate joint normal limit on Fibonacci intervals. Section 4 gives a direct cancellation proof of the cumulative ratio $(5-\sqrt5)/2$ and an all-prefix error bound. Deep Bhattacharjee and Ushashi Bhattacharya had already proved the ratio and the mixed-weight first-occurrence formula in October 2026. [Earlier preprint](https://hexagonmath.org/2610.00478v1) · [Lean ratio theorem](Ratio.lean)

## Verification

The Lake package uses Lean 4.19.0 and the pinned mathlib revision in the manifest. Its theorems start from subtraction of the actual largest available coin. The identification of ordinary Wythoff pairs uses the Beatty partition theorem in mathlib. The joint generating function and the analytic joint limit have written proofs. [Ordinary-array coverage and both row classifications](Wythoff.lean) The independent Python audit uses only the standard library. It compares the equalities against 350,000 consecutive inclusive prefixes and tests the row formulas against Morrison’s original construction in 2,000 rows.

```sh
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

[Build and audit results](verification.txt) · [Greedy definitions](Greedy.lean) · [Prefix proof](Dominance.lean) · [Block estimates](Mixed.lean) · [Audit source](verify.py)
