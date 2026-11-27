# Factor frequencies and fifth powers in the base-3/2 Thue–Morse words

This manuscript proves Conjectures 7–10 of Michel Dekking's 2023 journal paper. The sequence in those conjectures is OEIS A357448, denoted by $x$. The normalized base-3/2 digit-sum parity sequence is denoted by $t$. Each bit $b$ of $t$ gives the triple $(b,1-b,b)$ of $x$. [Original conjectures, pp. 3–4](https://cs.uwaterloo.ca/journals/JIS/VOL26/Dekking/dek25.pdf) · [Manuscript (PDF)](base-three-halves.pdf) · [LaTeX source](base-three-halves.tex)

| Journal conjecture | Result |
| --- | --- |
| 7. Factor frequencies | Every finite binary word has an exactly computable rational frequency in each sequence. In $x$, `00` has frequency $1/10$ and `01` has frequency $2/5$. |
| 8. Complement | Switching every zero and one in a word preserves its frequency. |
| 9. Reversal | Reading a word backwards preserves its frequency. |
| 10. Critical exponent, attributed to Shallit | Both sequences have critical exponent five. The only fifth powers in $x$ are five copies of `010` and five copies of `101`. Each has frequency $1/180$. |

The frequency result holds even if the allowed starting positions are restricted to one residue class modulo any power of two. For example, among starts of the form $8j+3$, the fraction beginning with `00` still tends to $1/10$ in $x$.

The frequency argument uses Theorem 18 of Cassaigne, Espinoza, Rigo and Stipulanti, which gives the frequency of single bits of $t$ in dyadic residue classes. The formal proof takes the precise limit in that paper as its argument, converts the denominator to the number of progression terms, and derives the limits for all words. The repetition proof uses only the defining recurrences. [Single-letter frequency theorem, Section 3](https://arxiv.org/html/2602.21895v1)

## Proofs and calculation

- [Dekking.lean](Dekking.lean) states the external single-letter result as `GlobalLetterTheorem` and derives `factor_frequencies`, `conjectured_values`, and `fifth_frequencies`.
- [Repetitions.lean](Repetitions.lean) proves the period bounds for all starts, lengths and periods, classifies fifth powers and verifies witnesses in both words.
- [Decoding.lean](Decoding.lean), [Estimates.lean](Estimates.lean), [Frequencies.lean](Frequencies.lean), [Sibling.lean](Sibling.lean), and [Symmetry.lean](Symmetry.lean) give the exact rational recursion, counting estimates, convergence and symmetry proofs.
- [frequencies.py](frequencies.py) evaluates the rational frequency of a binary word. [verify.py](verify.py) checks it against literal inverse images, word-frequency identities, and a million directly generated bits of each sequence. [Verification output](verification.txt)

Run these commands from this directory. The calculator defaults to Dekking's word.

```sh
python3 frequencies.py 00                     # 1/10
python3 frequencies.py 010010010010010         # 1/180
python3 frequencies.py --normalized 00        # 3/10
python3 verify.py
lake exe cache get
lake build
sha256sum -c SHA256SUMS
```
