# Drawing every chord between marks on a polygon

**Blake Stone · Proof developed with OpenAI Codex.**

In November 2023 Scott R. Shannon and N. J. A. Sloane proposed quartic formulas for the numbers of regions, vertices, and edges obtained by joining every pair of boundary marks on a regular polygon. The marks include the corners and a fixed number of additional points on each side. One count of four-point subsets proves the proposed rows and gives a formula for every number of sides. [Regions, A366253](https://oeis.org/A366253) · [Vertices, A367183](https://oeis.org/A367183) · [Edges, A367190](https://oeis.org/A367190)

## Theorem

Start with a regular $n$-gon, $n\ge3$, with all its diagonals drawn. Let $V_0,E_0,R_0$ be its counts of vertices, edges, and bounded regions, including the corners and boundary edges. Mark $k\ge0$ additional points inside each side, and join every pair of boundary points by a straight segment. Assume the added points are in general position: every interior crossing involving a chord with an added endpoint is simple. The original diagonals may have any number of concurrent lines.

Put $b=n(k+1)$, the number of boundary points, and $h=k+2$, the number lying on any one closed side. Define

$$
H=\frac{n(n-1)}2 k^2+n(n-2)k
$$

and

$$
J=\binom b4-\binom n4-n\left[\binom h4+(b-h)\binom h3\right].
$$

Binomial coefficients with upper index smaller than the lower index are zero. The counts after the new chords are drawn are

$$
\begin{aligned}
V &= V_0+nk+J,\\
E &= E_0+nk+H+2J,\\
R &= R_0+H+J.
\end{aligned}
$$

The original counts are established sequences: $V_0$ is [A007569](https://oeis.org/A007569), $E_0$ is [A135565](https://oeis.org/A135565), and $R_0$ is [A007678](https://oeis.org/A007678). Poonen and Rubinstein give explicit formulas for the original interior intersections and regions in [*The Number of Intersection Points Made by the Diagonals of a Regular Polygon*](https://arxiv.org/abs/math/9508209). Their result supplies the constants in these quartics, including all effects of concurrent original diagonals.

## Proof

There are $\binom b2-n\binom h2$ chords whose interior lies inside the polygon: subtract the pairs on the same side, each of which belongs to just one side. Subtract the original $\binom n2-n$ diagonals and expand. The difference is $H$, the number of added interior chords.

Choose four distinct boundary points. If no three lie on one side, they form a strictly convex quadrilateral; exactly its two diagonals cross in the interior. Conversely every crossing pair of chords determines such a four-point set by taking the endpoints. A set with at least three collinear points has no interior crossing. Indeed any line meeting a convex polygon in three boundary points must be a supporting line along a side.

On a given side there are $\binom h4$ sets with four points on the side and $(b-h)\binom h3$ sets with exactly three. No set of four can contain three points on each of two different sides, since two sides share at most one point. Thus $\binom b4-n[\binom h4+(b-h)\binom h3]$ counts all crossing **pairs** of chords, including pairs that cross where other chords also meet.

Precisely $\binom n4$ of those pairs consist of two original diagonals. Removing these leaves $J$ pairs involving at least one new chord. Their crossings are simple by hypothesis, so they give $J$ distinct new interior vertices. In particular, a new chord cannot pass through a crossing of two original diagonals. The additional $nk$ boundary marks give $V-V_0=nk+J$.

Each boundary mark splits one boundary edge. Each new chord contributes one edge before its internal subdivisions are counted. Each of the $J$ new crossings contributes one subdivision on each of its two participating chords, including subdivisions on original diagonals. Hence $E-E_0=nk+H+2J$. Both graphs are connected. Euler's formula for bounded regions gives $R-R_0=(E-E_0)-(V-V_0)=H+J$. This proves all three identities.

## The proposed rows

For example the square has $(R_0,V_0,E_0)=(4,5,8)$. Substituting $n=4$ gives

$$
\begin{aligned}
R &= (17k^4+38k^3+43k^2+28k+8)/2,\\
V &= (17k^4+38k^3+31k^2+20k+10)/2,\\
E &= 17k^4+38k^3+37k^2+24k+8.
\end{aligned}
$$

These are the square formulas, including the region conjecture in [A367121](https://oeis.org/A367121). For the triangle, $R=(9k^4+12k^3+15k^2+12k+4)/4$, proving [A367118](https://oeis.org/A367118).

For all eight rows listed in the three arrays, the following table gives $4J$ in descending powers of $k$, followed by the known starting counts. The constant coefficient of $J$ is zero. Substituting these coefficients into the theorem reproduces the listed quartics.

| $n$ | $[k^4]4J$ | $[k^3]4J$ | $[k^2]4J$ | $[k]4J$ | $R_0$ | $V_0$ | $E_0$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 9 | 12 | 3 | 0 | 1 | 3 | 3 |
| 4 | 34 | 76 | 62 | 24 | 4 | 5 | 8 |
| 5 | 90 | 240 | 240 | 110 | 11 | 10 | 20 |
| 6 | 195 | 570 | 627 | 312 | 24 | 19 | 42 |
| 7 | 371 | 1148 | 1337 | 700 | 50 | 42 | 91 |
| 8 | 644 | 2072 | 2508 | 1360 | 80 | 57 | 136 |
| 9 | 1044 | 3456 | 4302 | 2394 | 154 | 135 | 288 |
| 10 | 1605 | 5430 | 6905 | 3920 | 220 | 171 | 390 |
