# The positions, lengths and levels of all partition plateaus

Omar E. Pol conjectured which values repeat in each column of A195825 and how long each repeat lasts. In column $k$, the plateau indexed by $r$ starts at row $r(k+3)$ and has length $k+1-2r$, for $0\le r\le\lfloor(k-1)/2\rfloor$. These are all maximal runs of length at least two. Their levels are the cumulative counts of three-colored partitions through weight $r$. Independent mathematical review is pending. [Manuscript (PDF)](partition-plateaus.pdf) · [LaTeX](partition-plateaus.tex) · [A195825](https://oeis.org/A195825)

For example, column six has seven ones, five fours and three thirteens starting at rows 0, 9 and 18. Jacobi's triple product turns each column into a partition count. Taking its first difference removes the part one, leaving three generators whose consecutive sums describe every gap. The result also derives the Euler-transform formula queried in A210843 and used there by Václav Kotesovec. [A210843](https://oeis.org/A210843)

Run `python3 verify.py` to compare the polygonal-number recurrence with the predicted start, length and value of every plateau in the first 40 columns. [Verifier](verify.py)
