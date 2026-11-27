# Distinct circles determined by two rows of grid points

**Blake Stone · Proof developed with OpenAI Astra 6.2.**

In June 2025 Scott R. Shannon and N. J. A. Sloane conjectured a formula for the number of distinct circles through at least three vertices of a $2\times n$ grid. The count hinges on the circles through four vertices: their two horizontal chords must have the same perpendicular bisector. [OEIS A384700](https://oeis.org/A384700)

## Theorem

Let $a(n)$ count these circles on the rows $\{0,\ldots,n-1\}\times\{0,1\}$. For every $n\ge1$,

$$
a(n)=\frac{2n^3-n^2-4n+3\,\mathbf{1}_{n\text{ odd}}}{4}.
$$

This proves both parity cases in A384700. The formula also gives $a(1)=0$.

## Count triples, then correct for repetitions

A noncollinear triple consists of two points on one row and one point on the other. There are

$$
T=2n\binom{n}{2}=n^2(n-1)
$$

such triples, and each determines a unique circle. A circle meets each row in at most two points. Thus each circle counted by $a(n)$ contains either three or four grid points. A three-point circle contributes one triple; a four-point circle contributes four. Writing $Q$ for the number of four-point circles gives $a(n)=T-3Q$.

Consider two distinct columns $i<j$ in the bottom row and $u<v$ in the top row. The four points are concyclic if and only if $i+j=u+v$. Indeed, the center of any such circle must lie on the perpendicular bisector of each horizontal chord, so their midpoints must have the same horizontal coordinate. Conversely, draw the circle through the two bottom points and the top point in column $u$. Its center lies on the vertical line $x=(i+j)/2$. If the sums agree, reflection in this line takes the top point in column $u$ to the top point in column $v$, which also lies on the circle. Each four-point circle determines precisely one such pair on each row.

Let $r_s$ be the number of pairs $0\le i<j<n$ with $i+j=s$. The choices on the two rows are independent for each fixed $s$, so

$$
Q=\sum_s r_s^2.
$$

For $0\le s\le n-1$, choosing $i$ from $0$ through $\lfloor(s-1)/2\rfloor$ gives $r_s=\lfloor(s+1)/2\rfloor$. Reflecting the columns in the midpoint of the row gives $r_{2n-2-s}=r_s$. Consequently

$$
\begin{aligned}
Q(2m)&=4\sum_{j=1}^{m-1}j^2+m^2
       =\frac{4m^3-3m^2+2m}{3},\\
Q(2m+1)&=4\sum_{j=1}^{m-1}j^2+3m^2
       =\frac{4m^3+3m^2+2m}{3}.
\end{aligned}
$$

In the first line the peak multiplicity $m$ occurs once; in the second it occurs three times for $m\ge1$. Every smaller positive multiplicity occurs four times. For $n=1$ there are no pairs. Substitution into $a(n)=n^2(n-1)-3Q(n)$ proves the formula.

For example, the three unordered column pairs on the $2\times3$ grid have distinct sums. This gives three four-point circles and $18-3\cdot3=9$ distinct circles in all.

## Source

Scott R. Shannon and N. J. A. Sloane, [The On-Line Encyclopedia of Integer Sequences, A384700](https://oeis.org/A384700), June 7, 2025.
