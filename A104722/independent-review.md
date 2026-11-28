# Independent review: A104722

Review date: **2026-11-28**. Reviewer: a separate proof-review agent that did not author or restore this package's Lean development. Outcome: **PASS for the recurrence for every `n≥4` and the `n=3` exception**.

This review combines mathematical and source inspection with a new source-only compilation. It is not an external peer review or a claim of worldwide priority. The author and reviewer use the same pinned Lean compiler and external libraries, but separate local build directories and compiled proof objects.

## Source binding and endpoints

I compared both Lean modules and the human manuscript with the frozen A104722 source. `repeated n` is exactly the Catalan number `C(n/2)` under natural-number division, so every Catalan number is repeated twice. `source n` is the full convolution from `k=0` through `k=n`. It is not defined using the desired recurrence or its parity consequences.

The initial values are `1,2,3,4`, starting at index zero. The exceptional zero term is retained: the positive even formula `a(2r+2)=C(r+2)+C(r+1)` is never applied at index zero. This distinction is the reason the recurrence does not extend to `n=3`.

The related A059348 source has a different displayed leading term and OEIS offset. The development does not silently substitute it for A104722 or use it as a theorem assumption.

## Mathematical and manuscript review

1. **Odd convolution.** Pairing `k=2j` and `k=2j+1` at `n=2r+1` gives two copies of `C(j)C(r−j)`. The finite-sum proof handles all indices and yields `a(2r+1)=2C(r+1)` for every `r≥0`.
2. **Even convolution.** At `n=2r+2`, the even summands form the Catalan convolution of degree `r+1`, while the odd summands form the convolution of degree `r`. The proof separately handles the unpaired final even summand. This yields `a(2r+2)=C(r+2)+C(r+1)` without assuming an invalid formula at zero.
3. **Catalan ratio.** `catalan_ratio` derives `(r+2)C(r+1)=2(2r+1)C(r)` from mathlib's central-binomial-coefficient identities. It cancels the positive factor `r+1` in the natural numbers and then casts the exact identity to integers. There is no division by a potentially zero quantity.
4. **Recurrence certificates.** With `H(r)=(r+2)C(r+1)−2(2r+1)C(r)`, the two residual identities are `R(2r+4)=2H(r+2)+6H(r+1)` and `R(2r+5)=6H(r+2)+2H(r+1)`. I checked their expanded coefficients against the manuscript and the Lean linear combinations. They vanish for all `r≥0` and cover every `n≥4`.
5. **Sharp cutoff.** The final theorem explicitly assumes `4≤n`; all source indices then remain in range. The separate theorem gives `R(3)=7·4+4·3−16·2−4·1=4`. Thus extending the displayed recurrence to the preceding natural index would be false. The manuscript and README state this qualification prominently.

No blocking statement mismatch or mathematical gap was found. The proof establishes the recorded recurrence and its cutoff from the literal convolution; it does not claim that the classical Catalan convolution, ratio identity or parity formulas are newly discovered.

## Prior-work qualification checked

The frozen A104722 source credits James Sellers's 2008 generating-function observation relating the sequences after their differing first terms. I also independently read Theorem 3.7 of [Zhao, Li and Sun's 2025 paper](https://ccj.pku.edu.cn/Article/DownLoad?id=661522580062277&type=ArticleFile). Its permutation enumeration for `n≥3` uses the same relevant Catalan parity expressions. The manuscript credits that related result and makes no novelty claim for those formulas. This review of the cited material does not establish global priority for the particular recurrence proof or its formalization.

## Fresh compilation and axiom audit

The independent build copied only Lean sources and pinned package configuration into a new directory, without local `.olean` files from the original package or author build. Both `Source` and `Proof` were explicit roots. They compiled successfully with Lean **4.19.0** and mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

The build helper checked all local Lean code for `sorry`, `admit`, custom `axiom` declarations and `native_decide`. The printed principal theorem audits depend only on `propext`, `Classical.choice` and `Quot.sound`. One nonblocking style linter warning concerns an unnecessarily focused tactic sequence; it does not affect proof acceptance. The complete real build output is in [independent_build.log](independent_build.log).

Reviewed Lean SHA256 values:

| File | SHA256 |
|---|---|
| `Source.lean` | `ec8bbf26087787067b63787d97de3ca85623c9a0ba9ef755091800a34e537bda` |
| `Proof.lean` | `1125d4b43fcd9de29d9a5dc601e7fb87000e5b09197bcd2e5da8ca5eca1ae36e` |

## Supplementary replay

I reran the supplied Python/SymPy checker after compilation. It checked snapshot sizes and SHA256 hashes, all **35** frozen source terms, the parity identities through index **200**, residual **4** at index **3**, vanishing residuals at every index **4 through 200**, and both symbolic linear-combination certificates. Its real output is appended to [independent-verification.txt](independent-verification.txt).

That replay is a separate execution of the supplied checker, not a separately authored verification algorithm. Finite checks supplement the unbounded Lean theorem and the mathematical review above.
