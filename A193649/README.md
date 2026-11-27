# Ten formulas for triangular-array residues

Clark Kimberling defined a residue by repeatedly replacing a monomial with the preceding row of a triangular array. The manuscript derives ten formulas proposed by R. J. Mathar from those downsteps. For the all-ones array, the entire transform reduces to evaluating a row polynomial at one-half and adding an endpoint correction. Independent mathematical review is pending. [Manuscript (PDF)](triangle-residues.pdf) · [LaTeX](triangle-residues.tex)

| Source entries | Result |
| --- | --- |
| [A193649](https://oeis.org/A193649), [A193656](https://oeis.org/A193656), [A193661](https://oeis.org/A193661), [A193662](https://oeis.org/A193662) | Rational generating functions for the Fibonacci, geometric, binomial-mixture and Lucas rows |
| [A193654](https://oeis.org/A193654), [A193655](https://oeis.org/A193655) | The two rounded row sums and their rational generating functions |
| [A193658](https://oeis.org/A193658), [A193659](https://oeis.org/A193659) | Two instances of a four-step recurrence for every affine kernel $q(i,j)=i+j+c$ with binomial input |
| [A193663](https://oeis.org/A193663), [A193665](https://oeis.org/A193665) | The Fibonacci-row generating function and a three-step polynomial-coefficient recurrence |

The proof follows the original programs and data. The manuscript identifies a Fibonacci coefficient-order distinction, quotients printed in place of products in the rounded titles, conflicting triangle assignments in A193658 and A193659, and an incorrect cross-reference in A193665. It gives the outcomes of the alternative readings where the titles specify usable arrays.

Run `python3 verify.py` for 90 downsteps per sequence. Adding `--oeis-repo /path/to/oeisdata` also checks the terms published in all ten source entries. [Verifier](verify.py) · [OEIS data revision](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b)
