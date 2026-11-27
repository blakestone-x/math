# Squares split into two blocks with a prescribed difference

Michel Lagneau asked whether every positive square $n^2$ occurs as the difference between the two equal-length decimal halves of another square. The construction gives infinitely many witnesses for every $n$, in every integer base $b\ge2$. The least witnessing root has order $n^2$ for each fixed base. [A236383](https://oeis.org/A236383)

In decimal, choose any sufficiently large odd $d\equiv4n\pmod{11}$ and put $k=5(10^d+1)/11+n$. Dividing $k^2$ into two $d$-digit blocks gives the required difference. For example, $464^2=215296$ and $296-215=81$.

Giovanni Resta also asked about prescribed differences that are arbitrary integers. His entry reports a search past $10^{70}$ for a difference of seven. Quadratic reciprocity rules out seven at every width. The same obstruction rules out $7\cdot10^{2h}$ for every $h\ge0$. A separate construction realizes every difference $2n^2$ at infinitely many decimal widths.

[Manuscript](concatenated-squares.pdf) · [LaTeX source](concatenated-squares.tex) · [Lean proof of the decimal square-gap construction](DecimalWitness.lean) · [Arithmetic checks](verify.py)

Lean 4.19.0 with its standard library checks `lean DecimalWitness.lean`. The theorem gives witnesses for every $n,t\ge0$ at width $26n+11+22t$, including both digit bounds. Run `python3 verify.py` with SymPy to test the constructions and the Jacobi-symbol calculation.

## Which literal differences occur?

For a set of primes of relative density $227568931/268435456$ (about 84.776%), every difference $pm^2$ with $m\ge1$ occurs at infinitely many decimal widths. The proof lifts a square root modulo $10^d+1$ to one modulo $10^{dp}+1$ by a quadratic Gauss sum. For example, the seed $14^2\equiv701\pmod{101}$ gives an explicit square with two 1,402-digit halves differing by 701.

| Difference | All square roots when the witness set is finite and nonempty |
|---:|---|
| 3 | 5 and 6 |
| 6 | 39 and 62 |
| 24 | 78 |
| 30 | 38 and 63 |

Among differences 0 through 1000, the table gives 860 explicit witnesses and the modular calculation excludes 67 other differences at every width. These two certificates leave 74 undecided. Each root has been checked by squaring and splitting at the stated place.

[Manuscript](prime-gaps.pdf) · [LaTeX source](prime-gaps.tex) · [Witnesses](gap-witnesses.csv) · [Impossible differences](absent-gaps.txt) · [Verifier](verify-prime-gaps.py) · [Large-prime certificates](prime-certificates.txt)

Run `python3 verify-prime-gaps.py` with SymPy. To replay the four large-factor primality certificates, compile Dana Jacobsen’s standalone checker with `cc -O2 -o vcert vcert.c -lgmp -lm` and pass its path with `--vcert ./vcert`. All remaining factors are checked by trial division. [Checker source](https://github.com/danaj/Math-Prime-Util-GMP/blob/531591c6aa56c0f42450b8ca202dac56ab573b43/examples/vcert.c) · [Cunningham factor tables](https://homes.cerias.purdue.edu/~ssw/cun/)
