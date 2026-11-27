# Four-tile intersections in strips tiled by bars

Blake Stone · Proof developed with OpenAI Codex.

Richard J. Mathar recorded generating-function conjectures for tilings of a rectangle by congruent bars, classified by the number of points where four tiles meet. We give a common proof for the strips whose height equals the bar length. The formulas below prove Conjectures 1, 2, 5, 7, 10, 11, 13, 14, 19 and 20 as stated, and correct a sign in Conjecture 12. These are specializations of one word enumeration. The separate three-row domino case is [proved here](README.md). [Mathar, *Paving Rectangular Regions with Rectangular Tiles*, arXiv:1311.6135v1](https://arxiv.org/html/1311.6135v1)

## Counting before identifying symmetries

Fix $k\ge2$. Tile a $k\times n$ board by $1\times k$ bars in either orientation. Each tiling is a unique word in two letters. A vertical bar $V$ fills one column. If no vertical bar meets the leftmost column, every one of its $k$ cells must start a horizontal bar, producing a $k\times k$ block $H$. Remove the first block and repeat. Give the letters weights $z$ and $h=z^k$, respectively, so the total exponent of $z$ records the board length.

The only four-tile intersections are at interfaces between consecutive $H$ blocks. At each such interface there is one four-tile junction at each of the $k-1$ interior row boundaries. All other interfaces have a single vertical bar on at least one side. Thus $j$ occurrences of $HH$, counting overlaps, give exactly $(k-1)j$ four-tile intersections.

Let $L_j(z)$ count words with exactly $j$ occurrences, and put $D(z)=1-z-zh=1-z-z^{k+1}$. If $u$ marks an occurrence, a possibly empty string of consecutive $H$'s has series

$$
S=1+\frac{h}{1-uh}.
$$

Splitting a word at its individual $V$'s gives its sequence of such strings, so

$$
\sum_{j\ge0}L_j(z)u^j=\frac{S}{1-zS}
=\frac{1+h-uh}{D(z)-uh(1-z)}.
$$

Expanding in $u$ and using $(1+h)(1-z)-D(z)=h$ gives

$$
L_0(z)=\frac{1+h}{D(z)},\qquad
L_j(z)=\frac{h^{j+1}(1-z)^{j-1}}{D(z)^{j+1}}\quad(j\ge1).
$$

All intersection counts not divisible by $k-1$ have zero generating function.

## Identifying symmetric tilings

For nonsquare boards, top-bottom reflection fixes every word, and left-right reflection reverses it. Thus the number of orbits of a given length and intersection count is half the sum of the word count and the palindrome count. At $n=k$ the square also admits a quarter-turn, which merges the two tilings $H$ and $V^k$. Both have zero intersections. Consequently the unrestricted and zero-intersection orbit series each require subtraction of $h=z^k$.

The series for all words is $L=1/(1-z-h)$. A palindrome consists of an arbitrary half-word and its reflection, optionally separated by one central letter. Its series is $(1+z+h)/(1-z^2-h^2)$. Write $O,O_0,O_1$ for the orbit series without a restriction, with zero $HH$ occurrences, and with one occurrence, respectively. Then

$$
O=-h+\frac12\left(\frac{1}{1-z-h}+
\frac{1+z+h}{1-z^2-h^2}\right).
$$

For zero occurrences, the series for an empty word or a word avoiding $HH$ and ending in $V$ is $1+zL_0=1/D(z)$. To form a palindrome with no $HH$, a half-word of this type permits an empty center or a central $H$. A central $V$ permits any half-word avoiding $HH$. The half-word is copied twice, so this gives

$$
O_0=-h+\frac12\left(\frac{1+h}{D(z)}+
             \frac{1+z+h+zh^2}{D(z^2)}\right).
$$

For exactly one $HH$, reversal must fix that unique occurrence, so the two $H$'s are the central pair. The word to their left is empty or ends in $V$ and avoids $HH$. Thus the palindrome series is $h^2/D(z^2)$. Averaging with $L_1$ yields

$$
O_1=\frac{h^2}{2}\left(\frac{1}{D(z)^2}+\frac{1}{D(z^2)}\right).
$$

## Comparison with the numbered formulas

| $k$ | Conjecture and equation in Mathar | Specialization |
|---:|---|---|
| 2 | 1 (12), 2 (13) | $L_1,L_2$ |
| 2 | 5 (24) | $O_1$ |
| 3 | 7 (30) | $L_j$ for every $j\ge1$, and zero for odd intersection counts |
| 3 | 10 (34), 11 (35) | $O,O_0$ |
| 3 | 12 (36), corrected below | $O_1$ |
| 4 | 13 (37), 14 (38) | $L_1,L_2$ |
| 4 | 19 (43), 20 (44) | $O_0,O_1$ |

These identities follow by substituting $h=z^k$ and clearing denominators. The [exact algebra checks](verify.py) give each comparison explicitly. For $k=4$, the factorization $1-z-z^5=(1-z+z^2)(1-z^2-z^3)$ explains the alternative denominators. Mathar already linked the unrestricted and zero-crossing counts for $k=3$ with existing composition sequences. [A102543](https://oeis.org/A102543) · [A192928](https://oeis.org/A192928)

In equation (36) as printed, the coefficient of $z^2$ is $1$. On a $3\times2$ board the only tiling consists of two vertical bars, giving zero four-tile intersections, as recorded in Mathar's Table 25. The first board with two intersections has length six. In the paper's notation, replacing the plus immediately before $1/(1-z-z^4)$ with a minus gives the correct series: the first two fractions in brackets then combine to $z^4/(1-z-z^4)^2$, yielding exactly $O_1$ above.
