# Diagonals and populations of five von Neumann cellular automata

The center-to-corner diagonal of rule 62 begins with an off cell at every stage n ≥ 2, followed by exactly floor(n/2) on cells and then ceil(n/2) off cells. Rules 65, 321 and 323 have an alternating cross giving the exact configuration at every stage from 5 on. Rules 65 and 321 agree at all times. Rule 323 differs from them only at stage 1. Rule 73 becomes spatially uniform at stage 4. [Manuscript](diagonals.pdf) · [LaTeX source](diagonals.tex)

For rules 65 and 323 the number of live cells inside the stage-n window is 2n + 5 at even stages and 4n² − 2n + 6 at odd stages for n ≥ 5. This determines the dyadic samples, partial sums, and first differences as well as ten diagonal encodings. The paper credits Robert Price, Colin Barker, and Lars Blomberg and gives the source entry for each statement.

| OEIS entries | Readout | First index from which the displayed homogeneous recurrence always holds |
|---|---|---|
| A285612, A285613 | Rule 62 diagonals | 5 |
| A285643–A285646 | Rule 65 diagonals | 9 |
| A285647–A285650 | Rule 73 diagonals | 8 |
| A269782, A270569 | Populations of rules 65 and 323 | 11 |
| A270084, A271254 | Populations at stages 2ⁿ − 1 | 5 |
| A270085, A271255 | Partial sums | 11 |
| A270086, A271256 | First differences | 10 |

All sixteen conjectured generating functions among these eighteen entries agree with the proofs. Ten of their proposed recurrence ranges have exceptions. The verification record gives each numerator and every exceptional index. The two entries A270569 and A271255 also acquire explicit rational generating functions in the paper. [Verification record](verification.txt)

## Reproduction

From this directory, with the pinned Lean 4.19.0 toolchain and Python 3 installed, run the following commands.

~~~sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
~~~

[Automaton.lean](Automaton.lean) proves that the reflected evaluator obeys the original rule on the integer lattice. [Checkerboard.lean](Checkerboard.lean) proves the rule-62 invariant and [Cross.lean](Cross.lean) handles the alternating crosses and rule 73. [Readouts.lean](Readouts.lean) proves the diagonal words and their radix evaluation. [Population.lean](Population.lean) counts the cells and [Agreement.lean](Agreement.lean) treats the complete rule coincidence and the population formula from stage 5. The manuscript derives the rational series. [Independent simulator and coefficient audit](verify.py)
