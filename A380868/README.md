# Every triangular rectangle count occurs infinitely often

Blake Stone · Proof developed with OpenAI Codex.

Daniel Mondot’s second conjecture on OEIS A380868 asks whether every triangular number occurs as the number of rectangles formed from a cyclic chain of rods of lengths 1 through n. For each positive k, the manuscript constructs infinitely many chains with exactly k pairs of opposite joints in each of the two possible congruence classes of n modulo four. Any two such pairs determine a rectangle, so each triangular count occurs infinitely often.

The identity relating rectangle counts to pairs of folds was already known. The construction prescribes exactly which divisors of the perimeter produce folds. It also proves that the least index in A390056 exists for every positive fold count.

[Proof manuscript](rod-counts.pdf) · [LaTeX source](rod-counts.tex) · [Exact checks](verify.py) · [Mondot’s conjectures](https://oeis.org/A380868) · [Fold counts](https://oeis.org/A382605)
