# Fibonacci bounds for ordinary queen vertex denominators

Let $I_q$ be the largest integer such that every positive denominator through $I_q$ occurs at a vertex of the ordinary $q$-queens inside-out polytope. With $\varphi=(1+\sqrt5)/2$, the manuscript proves

$$I_q\;\ge\;\exp\!\big(q\log\varphi-O(q/\log q)\big).$$

Thus $\liminf I_q^{1/q}\ge\varphi$. Chaiken, Hanusa and Zaslavsky constructed a vertex with denominator $F_q$ and proposed the full initial interval through $F_q$. The finite endpoint in their Conjecture 6.2 remains open. The previous binary construction guaranteed the contiguous interval through $2^{\lfloor(q-1)/2\rfloor}$. [Original Conjecture 6.2](https://doi.org/10.1016/j.disc.2019.111649) · [Earlier construction](https://github.com/blakestone-x/math/blob/proof-fleet-2026-11-26/A342372/periods.pdf)

[Proof manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Exact rank and coordinate verifier](verify.py)

| Result | Quantitative statement |
|---|---|
| Finite construction | For $k\ge3$, let $b=F_k$ with $F_1=F_2=1$. Every denominator $d\ge2$ can be realized with at most $2b-1+(k+4)\lfloor\log_b d\rfloor$ labels. |
| No gaps | If $q\ge2b-1$ and $h=\lfloor(q-2b+1)/(k+4)\rfloor$, every integer $1\le d<b^{h+1}$ occurs. |
| Maximum for successive intersections | For every $q$, the exact largest denominator is $F_q$ among shapes formed from two attacking queens by repeatedly intersecting pairs of earlier attack lines. This proves Conjecture 6.1 for this class, including the attaining Fibonacci spiral. |
| Ordinary semiqueens | The same digit construction, applied to a semiqueen shape of side length proportional to $\rho^k$ where $\rho^3=\rho+1$, gives an unbroken interval through $\exp(q\log\rho-O(q/\log q))$. |
| Common vertex denominator | If $D_q$ is the least common multiple of all vertex denominators, then $\liminf (\log\log D_q)/q\ge\log\varphi$. |

The construction makes one copy of the discrete Fibonacci spiral for each nonleading digit of $d$ in base $F_k$. Two auxiliary queens set its scale equal to the current input, and two more add the next digit. Pinning the final coordinate to one makes a distinguished initial coordinate equal to $1/d$.

Run the verifier with Python 3. It checks both spans for 73 Fibonacci spiral sizes, constructs 515 ordinary queen vertices across eight radix choices, and checks 81 three-move semiqueen vertices. A separate exhaustive search of all successive-intersection shapes through seven queens obtains maxima 1, 2, 3, 5, 8 and 13. For each example it tests every attack and fixation equation, membership in the board, the least denominator, and full rank. The rank certificate uses a nonzero determinant modulo 1,000,003. The manuscript proves the unbounded construction.

```sh
python3 -B verify.py
```
