# Independent vertex sets in triangular grids

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

Let $G_n$ consist of the integer pairs $(x,y)$ with $x,y\ge0$ and $x+y\le n$. Neighbors differ by one of $\pm(1,0),\pm(0,1),\pm(1,-1)$. Thus $n$ counts edges on an outer side. Let $I_k(n)$ be the number of unordered sets of $k$ vertices with no adjacent pair. Eric W. Weisstein proposed an explicit polynomial for $I_7(n)$ for $n\ge4$. [OEIS A394659](https://oeis.org/A394659)

**Theorem.** For each fixed $k\ge1$, $I_k(n)$ agrees with a polynomial of degree $2k$ for all integers $n\ge\max(0,k-3)$. Its leading coefficient is $1/(2^k k!)$. For $k=7$, the polynomial is the formula in A394659.

## Proof of polynomiality

Label the $k$ vertices and initially permit arbitrary placements. Call a pair of labels bad if the vertices coincide or are neighbors. By inclusion–exclusion, we can count placements avoiding every bad pair from intersection counts for sets of required bad pairs.

Each set of required pairs forms a graph on the labels. In a connected component, anchor a root at the origin and follow a spanning tree. Each edge has seven allowed displacements, including zero. This gives finitely many relative placements. Retain those satisfying all required pairs in the component. Different components may translate independently, since this intersection imposes only the specified bad pairs.

For one relative placement set $s=\max(x+y)-\min x-\min y$, with the extrema taken over its vertices. Translate it so that both coordinate minima are zero. The number of ways to translate this normalized placement into $G_n$ equals the number of nonnegative integer pairs $(a,b)$ with $a+b\le n-s$. For $n\ge s$ the count is

$$
\frac{(n-s+1)(n-s+2)}{2}.
$$

The polynomial also gives the correct zero count at $n=s-1$ and $n=s-2$.

A component of $h$ labels has $s\le h-1$. Indeed, record each vertex as $(x,y,-x-y)$. Now $s$ is the negative sum of the three coordinate minima. Start with the root, for which $s=0$, and add vertices in tree order. A permitted displacement decreases at most one coordinate, by at most one. A new vertex can therefore lower the sum of the minima by at most one.

If $n\ge k-3$, then $n\ge s-2$ for every component. Thus every relative placement contributes a quadratic translation polynomial. A term with $c$ components, after summing relative placements and multiplying the component counts, has degree at most $2c$. Only the empty set of required bad pairs has $k$ components. Its contribution is $[(n+1)(n+2)/2]^k$. Dividing the count of valid labeled placements by $k!$ proves the degree and the leading coefficient.

## Identifying Weisstein's polynomial

Write $P(n)=(n-4)Q(n)/645120$. The coefficients of $Q$ in descending order are

~~~text
1, 25, 9, -3555, -7745, 260563, 291075, -11898033, 10339924,
303368632, -909281184, -2609966352, 16737321600, -23213352960
~~~

At $k=7$ the theorem gives degree 14 throughout $n\ge4$. Therefore exact equality at 15 distinct inputs proves the identity. The following counts were computed directly from grid adjacency.

| $n$ | $I_7(n)=P(n)$ | $n$ | $I_7(n)=P(n)$ | $n$ | $I_7(n)=P(n)$ |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 0 | 9 | 20,372,485 | 14 | 21,689,622,270 |
| 5 | 27 | 10 | 118,262,442 | 15 | 60,049,653,202 |
| 6 | 6,715 | 11 | 545,477,655 | 16 | 154,055,280,120 |
| 7 | 196,899 | 12 | 2,114,805,415 | 17 | 370,344,275,691 |
| 8 | 2,547,420 | 13 | 7,155,153,144 | 18 | 841,651,316,923 |

To reproduce the counts, process the diagonals $x+y=0,1,\ldots,n$ in that order. A mask on a diagonal records occupied positions indexed by $x$ and has no consecutive set bits. A new mask occupying position $i$ excludes positions $i$ and $i-1$ on the previous diagonal. For each new mask with $h$ bits and each total $j$, sum the preceding counts of size $j-h$ over all compatible masks. Initialize the empty row with one placement of size zero. Sum the final counts of size seven over all masks.

The verifier evaluates this recurrence and compares the integer counts with the polynomial at every $n$ from 4 through 20. It requires Python 3.10+ and NumPy. Run the following command from the repository root.

~~~sh
python A394659/verify.py
~~~

[Executable verifier](verify.py) · [Proof notes and certificate, pages 3–4](../notes/OEIS_Proof_Notes.pdf)
