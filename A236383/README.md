# Squares split into two blocks with a prescribed difference

Michel Lagneau asked whether every positive square $n^2$ occurs as the difference between the two equal-length decimal halves of another square. The construction gives infinitely many witnesses for every $n$, in every integer base $b\ge2$. The least witnessing root has order $n^2$ for each fixed base. [A236383](https://oeis.org/A236383)

In decimal, choose any sufficiently large odd $d\equiv4n\pmod{11}$ and put $k=5(10^d+1)/11+n$. Dividing $k^2$ into two $d$-digit blocks gives the required difference. For example, $464^2=215296$ and $296-215=81$.

Giovanni Resta also asked about prescribed differences that are arbitrary integers. His entry reports a search past $10^{70}$ for a difference of seven. Quadratic reciprocity rules out seven at every width. The same obstruction rules out $7\cdot10^{2h}$ for every $h\ge0$. A separate construction realizes every difference $2n^2$ at infinitely many decimal widths.

[Manuscript](concatenated-squares.pdf) · [LaTeX source](concatenated-squares.tex) · [Lean proof of the decimal square-gap construction](DecimalWitness.lean) · [Arithmetic checks](verify.py)

Lean 4.19.0 with its standard library checks `lean DecimalWitness.lean`. The theorem gives witnesses for every $n,t\ge0$ at width $26n+11+22t$, including both digit bounds. Run `python3 verify.py` with SymPy to test the constructions and the Jacobi-symbol calculation.
