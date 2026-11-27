# Which square roots are curbed?

Clark Kimberling asked whether infinitely many nonsquare radicands succeed and infinitely many fail his fractional-part inequalities for the shift 1/2. Both occur. The successes have natural density zero, yet for every positive divisor $d$ of $a$, the nonsquare $a^2+d$ succeeds. This supplies at least $(1/2)\sqrt X\log X-O(\sqrt X)$ successful nonsquares up to $X$. The paper also treats every shift $1-1/q$ for integers $q\ge2$.

Boshernitzan and Ralston’s 2009 characterization of heavy rotations supplies the continued-fraction criterion. Applied to a nonsquare integer square root, it gives an exact finite test by one or two periods. The test confirms the 36 displayed successes through 84. In the inspected complement the second 34 should be 35. [Earlier theorem](https://arxiv.org/abs/0911.2054) · [A194469](https://oeis.org/A194469) · [Inspected A194470 revision](https://github.com/oeis/oeisdata/blob/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A194/A194470.seq)

[Manuscript](curbed-roots.pdf) · [LaTeX source](curbed-roots.tex) · [Exact verifier](verify.py)

Run `python3 verify.py` for the continued-fraction and integer-only checks.
