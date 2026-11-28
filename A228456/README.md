# Sun’s Catalan Hankel determinants

For OEIS A228456, let H(n) be the Hankel determinant of the binomial-square transform of the Catalan numbers. We prove the missing residue class in Sun’s first conjecture. For every m ≥ 0, H(4m+1) is congruent to 3 modulo 8. Across all indices the residues 1, 3 and 5 have frequencies 1/2, 1/4 and 1/4. Christopher Beach previously proved positivity, the modulo-four classification and Kotěšovec’s growth prediction of 9/4. [Beach’s preprint](https://doi.org/10.5281/zenodo.24438853) · [OEIS A228456](https://oeis.org/A228456)

The prime supplement proves Sun’s predicted congruence modulo p² for every odd prime p congruent to 2 modulo 3. For primes congruent to 1 modulo 3, it proves the prediction modulo p. The lift to p² remains an open step. [Prime supplement](a228456-prime-supplement.tex) · [Exact remaining sum](split-reduction/proof.md) · [Unit-root calculation](a228456-unit-root.md)

[Mathematical proof](a228456.tex) · [Binary classification](binary/proof.md) · [Lean classification theorem](binary/SunBinary.lean) · [Complete proof book](../notes/left-to-solve-2026-11-27/Proofs.pdf) · [Board statement](https://lefttosolve.com/p/oeis-a228456)

Run `python3 verify_a228456.py` and `python3 binary/verify.py` to reproduce the finite certificate. Lean 4.33.1 checks the complete output classification for the finite automaton. The determinant-to-automaton identification is proved in the manuscript.
