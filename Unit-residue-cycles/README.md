# A circular ordering of the units with every unit as an edge difference

Zhi-Wei Sun conjectured that for each odd modulus $n>2$, one can place its units in a circle so that the directed differences around the circle are also a full reduced residue system. He proved the prime-power case. The manuscript constructs a cycle for every odd modulus. [Original paper, Theorem 1.4 and Remark 1.4](https://arxiv.org/abs/1309.1679) · [Proof manuscript](manuscript.pdf) · [Editable LaTeX](manuscript.tex)

| Edge labels required to run through all units | Exact condition for $n>2$ |
|---|---|
| Consecutive directed differences | $n$ is odd. |
| Consecutive sums | $\gcd(n,6)=1$. |
| Both sets, on the same circle | $\gcd(n,6)=1$. |

The construction lifts through one prime power at a time. After a trip around the smaller circle the new coordinate has been multiplied by a primitive root. On every edge, multiplication by a unit carries all elements of the new coordinate bijectively to the required edge labels. Reordering the multipliers gives at least $L\binom{L-1}{L/2}$ oriented cycles at every lifting step, where $L$ is the length of the smaller circle.

Running `python3 -B verify.py` builds 753 circular orderings and checks all 473,812 cyclic differences. Whenever $3\nmid n$ it also checks all cyclic sums. [Verifier](verify.py) · [Recorded output](verification.txt)

Lean 4.19 with mathlib checks the two abstract steps in the lifting lemma. They prove that bijections on each fiber give a bijection on the whole set and that a transitive full-lap map gives a transitive orbit when the phases cover all fibers. The arithmetic choice of multipliers and the final classification are proved in the manuscript. Run `lake env lean /absolute/path/to/CycleLift.lean` inside a mathlib 4.19 project. [Lean source](CycleLift.lean)
