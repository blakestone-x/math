# Elementary symmetric functions of periodic prefixes

Take a repeating list of positive integers. From its first $n$ entries, omit exactly $r$ positions in all possible ways, multiply the remaining entries, and add. The manuscript gives the generating function at every fixed $r$. For the ten periods below, the least recurrence has order $d(r+1)$, where $d$ is the length of the repeating block. Independent mathematical review is pending. [Manuscript (PDF)](periodic-symmetric.pdf) · [LaTeX](periodic-symmetric.tex)

R. J. Mathar proposed specific generating functions and recurrences for the case $r=1$ in ten of Clark Kimberling’s OEIS entries. All ten follow from the same identity. Robert Israel previously verified A203233 in 2017. Related individual formulas appeared in A203160–A203163. [Israel’s verification](https://oeis.org/A203233) · [Related period-three formula](https://oeis.org/A203162)

| OEIS sequences | Periods in the same order | Least order for one omission |
| --- | --- | ---: |
| [A203164](https://oeis.org/A203164), [A203165](https://oeis.org/A203165) | $(4,1,2,3)$ and $(3,4,1,2)$ | 8 |
| [A203166](https://oeis.org/A203166) | $(1,2,3,4,5)$ | 10 |
| [A203167](https://oeis.org/A203167) | $(2,2,1)$ | 6 |
| [A203230](https://oeis.org/A203230), [A203231](https://oeis.org/A203231) | $(1,3)$ and $(3,1)$ | 4 |
| [A203232](https://oeis.org/A203232), [A203233](https://oeis.org/A203233) | $(2,3)$ and $(3,2)$ | 4 |
| [A203234](https://oeis.org/A203234), [A203235](https://oeis.org/A203235) | $(1,1,1,2)$ and $(1,1,1,3)$ | 8 |

If $P$ is the product of a full period and $E$ denotes the shift in $n$, then $(E^d-P)^{r+1}$ annihilates the sequence. It is the least annihilator over the rationals whenever $z^d-P$ is irreducible. All ten listed periods satisfy this condition. The proof factors the generating polynomial into complete periods and one prefix, then extracts the coefficient of $t^r$.

For a quick example, repeating $(1,3)$ and omitting one entry gives $1,4,7,24,33,108,\ldots$. The recurrence is $u(n+4)=6u(n+2)-9u(n)$ and the generating function is $x(1+4x+x^2)/(1-3x^2)^2$. [A203230](https://oeis.org/A203230)

Run `lean Periodic.lean` with Lean 4.19 to verify the one-omission recurrence for arbitrary natural-number prefixes and repeated blocks, and the ten proposed numerator lists. Run `python3 verify.py` for independent checks by subset enumeration and polynomial multiplication. The option `--oeis-repo /path/to/oeisdata` compares all 317 terms in the ten source entries. [Lean proof](Periodic.lean) · [Python verification](verify.py) · [OEIS data revision](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b)
