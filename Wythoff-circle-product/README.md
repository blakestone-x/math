# Knuth multiplication on Wythoff rows

The Wythoff row map takes Knuth's Fibonacci product to Peter Munn's multiplication of extended rows. The proof also determines the output column. With zero-based ordinary columns, it is the sum of the input columns plus 0, 2, or 4. All three offsets occur. [Manuscript](row-products.pdf) · [LaTeX source](row-products.tex) · [Munn's conjecture, OEIS A357097](https://oeis.org/A357097)

A second result gives the common divisor in Horadam's hypotenuse construction. For a primitive pair of consecutive row entries with absolute determinant D, the normalized interleaved sequence has absolute determinant (D/gcd(5,D))². Row 45 has D = 121 and gives 14641, contradicting the squarefree-part formula in Kenneth J. Ramsey's comment. [OEIS A022344](https://oeis.org/A022344)

| File | What it proves |
|---|---|
| [Product.lean](Product.lean) | The canonical integer pair, its multiplicative internal coordinate, and compatibility with Lunnon's floor formula |
| [Digits.lean](Digits.lean) | The original double Fibonacci sum agrees with the pair product for every pair of finite binary words, including all Zeckendorf expansions |
| [Rows.lean](Rows.lean) | Identification of row anchors and the exact product entry for all ordinary row and column indices |
| [Horadam.lean](Horadam.lean) | The interleaved recurrence, primitive gcd, determinant, Pythagorean identity, and counterexample |

## Reproduction

From this directory, with the pinned Lean 4.19.0 toolchain and Python 3 installed, run the following commands.

~~~sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
~~~

The array check generates ordinary Wythoff rows by their defining recurrence. It compares the location of each directly computed Zeckendorf product with the predicted row and column. [Verification record](verification.txt) · [Independent verifier](verify.py)
