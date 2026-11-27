# Rectangular hexomino tilings and four-tile meetings

**Blake Stone · Proof developed with OpenAI Codex.**

Richard J. Mathar's 2013 paper gives fourteen conjectured generating functions for tilings by $2\times3$ rectangles, numbered 21–34. Twelve hold as printed. In Conjecture 23 the numerator needs a positive $z^6$ term, as Mathar subsequently obtained in 2014. In Conjecture 31 the right side counts the empty tiling twice. Its positive-width coefficients are correct. We give direct proofs for all fourteen cases. [Original paper, §5](https://arxiv.org/html/1311.6135v1#S5) · [Mathar's 2014 transfer-matrix derivation, Eq. (34)](https://arxiv.org/pdf/1406.7788)

| Conjectures | Board height | Count | Result |
|---|---:|---|---|
| 21–22 | 6 | All tilings with one or two four-tile meetings | As printed |
| 23 | 8 | All tilings | Corrected sign, already obtained in 2014 |
| 24 | 8 | All tilings with no four-tile meeting | As printed |
| 25–30 | 5 | Symmetry classes, in total and with zero through four meetings | As printed |
| 31 | 6 | Symmetry classes in total | Subtract 1 from the printed right side |
| 32–33 | 6 | Symmetry classes with one or two meetings | As printed |
| 34 | 7 | Symmetry classes in total | As printed |

Let $z$ mark the width $n$. At a **meeting**, four tiles have corners at the same interior grid point. Write $T_t(z,h)$ for the count at height $h$ with $t$ meetings, and $T(z,h)$ for the total. A bar indicates that we identify tilings under the symmetries of the board. A square also admits quarter-turns. Width zero has one empty tiling with zero meetings, consistently with the generating functions starting at $n=0$ in Mathar's Definitions 3, 4, 7 and 8.

## Six rows, Conjectures 21, 22 and 31–33

At a fresh vertical edge, the tile heights from top to bottom must form either $(3,3)$ or $(2,2,2)$. In each case the tiles fill an entire block before any of them ends. Cutting off that block and repeating gives a unique word in the letters $A$ (width 2) and $B$ (width 3). The respective horizontal breaks are at heights $3$ and $2,4$. At a joint $AA$ there is one meeting, at $BB$ there are two, and a mixed joint has none. Mathar explicitly identifies this word statistic just before Conjecture 21.

Let $a=a(z,y)$ and $b=b(z,y)$ count nonempty words ending in $A$ and $B$, with $y$ marking meetings. Appending the final letter gives

$$
a=z^2(1+ya+b),\qquad b=z^3(1+a+y^2b).
$$

Thus $F=1+a+b$ counts every tiling. For explicit coefficient extraction, put

$$
D=(1-yz^2)(1-y^2z^3)-z^5,\qquad
a=\frac{z^2(1+z^3-y^2z^3)}{D},\qquad
b=\frac{z^3(1+z^2-yz^2)}{D}.
$$

Expanding at $y=0$ yields the formulas in Conjectures 21 and 22.

$$
[y]F=\frac{z^4(1+z)^2(z^2-z+1)^2}{(1-z^5)^2},
$$

$$
[y^2]F=
\frac{z^6(2+2z^2+2z^3+z^4-z^5+z^6-2z^7-z^9)}{(1-z^5)^3}.
$$

Reflection across the horizontal center line fixes each letter and reflection across the vertical center line reverses the word. Reversal orbits are counted by $(F+P)/2$, where $P$ counts palindromes. There is one extra identification when $n=6$. The only two words are $AAA$ and $BB$, both with two meetings, and a quarter-turn exchanges them. The full orbit series is therefore

$$
O(z,y)=\frac{F(z,y)+P(z,y)}{2}-z^6y^2.
$$

For the palindromes, let $a'=a(z^2,y^2)$ and $b'=b(z^2,y^2)$ count a nonempty left half together with its reversed copy. In a palindrome with an even number of letters, a half ending in $A$ creates weight $y$ at the middle, and a half ending in $B$ creates $y^2$. For an odd number of letters, insert a central letter. Its two neighboring joints are the same type, so their combined weight is $y^2$ for $AA$, $y^4$ for $BB$, and 1 for mixed joints. Including the empty and single-letter words gives

$$
P=1+z^2+z^3+a'(y+y^2z^2+z^3)+b'(y^2+z^2+y^4z^3).
$$

At $y=1$ this gives the corrected Conjecture 31,

$$
\bar T(z,6)=-z^6+\frac12\left(\frac1{1-z^2-z^3}
+\frac{1+z^2+z^3}{1-z^4-z^6}\right).
$$

The displayed right side of Mathar's Eq. (57) adds 1 to this expression, giving constant coefficient 2. Extracting the next two meeting counts from $O$ gives Conjectures 32 and 33,

$$
[y]O=z^4+\frac{z^7(1+z^2+z^3+z^5+z^7-z^{12})}{(1+z^5)(1-z^5)^2},
$$

$$
[y^2]O=z^6+\frac{z^8(1+z+z^2+3z^3+z^4+z^6-z^7-z^{10}-4z^{13}+2z^{18})}
{(1+z^5)(1-z^5)^3}.
$$

## Eight rows, Conjectures 23 and 24

Cut at every full-height vertical line that runs along tile edges. The resulting nonempty blocks have no such cut in their interior. At the left of a block there are four possible lists of tile heights,

$$
U=(2,2,2,2),\quad M=(3,2,3),\quad L=(2,3,3),\quad R=(3,3,2).
$$

A block starting with $U$ ends at width 3. For $M$ the two outer tiles have width 2 and the middle one has width 3. When the outer tiles end first, they leave disjoint gaps of height 3, each forcing another tile of that height. When the middle tile ends, the two outer tiles continue and force a new middle tile. The first full cut is at width 6.

For $L$, follow the top band of height 2 and the lower band of height 6. The top uses width-3 tiles. The lower band starts with $A$ and is tiled by the height-six blocks $A,B$ above. This separation persists until a full-height cut. Whenever the top tile ends inside a lower block, every tile in that lower block continues and the next top tile is forced. Whenever the lower block ends inside a top tile, only the six lower rows can be refilled. The first simultaneous end occurs when the lower word first reaches width divisible by 3. Each $B$ contributes zero modulo 3 and each $A$ contributes two. Thus the lower words of the irreducible blocks are precisely

$$
A B^i A B^j A,\qquad i,j\geq0.
$$

Every such word is feasible, and $R$ is the top-to-bottom reflection of $L$. With $q=z^3$, the generating function of irreducible blocks is

$$
G=q+q^2+\frac{2q^2}{(1-q)^2}.
$$

Arbitrary tilings are sequences of these blocks. Therefore

$$
T(z,8)=\frac1{1-G}=\frac{(1-q)^2}{1-3q+q^3-q^4}.
$$

At width 6 there are four tilings: $UU$ and one block each of types $M,L,R$. The negative $z^6$ term printed in the numerator of Conjecture 23 gives only two. Mathar's Table 51 already records four. His 2014 Eq. (34) gives the corrected function with a variable marking the number of tiles. Four tiles cover three columns of height eight. [Mathar (2014), Figure 13 and Eq. (34)](https://arxiv.org/pdf/1406.7788) · [OEIS A236583](https://oeis.org/A236583)

For Conjecture 24, require zero meetings. Within an $L$ or $R$ block the six-row band must alternate $A,B$, forcing $i=j=1$. Along its border with the two-row band, a meeting would require a simultaneous end, already excluded in the block interior. There is therefore one allowed block of each type. Their widths for $U,M,L,R$ are $3,6,12,12$. The possible horizontal breaks at either end are

| Type | Break heights |
|---|---|
| $U$ | $2,4,6$ |
| $M$ | $3,5$ |
| $L$ | $2,5$ |
| $R$ | $3,6$ |

The sets at a joint must be disjoint. Consequently $U$ alternates with $M$, and $L$ alternates with $R$. Starting with $U$ or $M$, two blocks contribute width 9. Starting with $L$ or $R$, each block contributes width 12. The resulting series is

$$
\begin{aligned}
T_0(z,8)
&=1+\frac{q+q^2+2q^3}{1-q^3}+\frac{2q^4}{1-q^4}\\
&=\frac{1+2q+3q^2+4q^3+5q^4+4q^5+3q^6}{1+q+q^2-q^4-q^5-q^6},
\end{aligned}
$$

as in Conjecture 24.

## Five and seven rows, Conjectures 25–30 and 34

At height 5 the ordered tile heights in a column are $(2,3)$ or $(3,2)$. At height 7 they are the three permutations of $(2,2,3)$. In either case each list has a unique interval of height 3. A change to a different list requires the old height-3 tile and at least one old height-2 tile to end at the same column boundary: the new height-3 interval changes position and overlaps at least one of the old height-2 intervals. From a fresh edge the unchanged height-3 band has tile widths 2, and the height-2 bands have tile widths 3. A first change can only occur at a multiple of 6. All tiles end together at the sixth column, so cutting there and iterating gives a unique word of width-6 blocks. Write $s=z^6$ throughout this section.

At height 5 the two letters are interchanged by top-to-bottom reflection and word order reverses under left-to-right reflection. A meeting occurs precisely between two equal adjacent letters: the bands within a block have no simultaneous interior end, and the horizontal break at either end identifies its letter. Quotient first by exchanging both letters. A nonempty word of $k$ letters is then specified uniquely by a binary string of length $k-1$, whose entries indicate whether successive letters are equal. The number of ones is the number of meetings. The remaining symmetry reverses this string. The empty tiling forms its own orbit.

Without a restriction on the number of ones, binary strings have generating function $1/(1-2s)$. Palindromic binary strings have generating function $(1+2s)/(1-2s^2)$, since their first half is arbitrary and any middle letter has two choices. Averaging by reversal gives

$$
\bar T(z,5)=1+\frac{s}{2}\left(\frac1{1-2s}+\frac{1+2s}{1-2s^2}\right)
=\frac14\left(1+\frac1{1-2s}\right)+\frac{1+s}{2(1-2s^2)},
$$

which is Conjecture 25. For exactly $t$ ones a binary string is specified by its $t+1$ nonnegative gaps of zeros. Reversal fixes the string exactly when the gaps are palindromic. Their paired lengths supply factors $(1-s^2)^{-1}$, and an unpaired central length supplies $(1-s)^{-1}$. Writing $j=t+1$ yields the all-$t$ formula

$$
\bar T_t(z,5)=\mathbf1_{t=0}
+\frac{s^{j}}2\left[
\frac1{(1-s)^{j}}+
\frac1{(1-s)^{j\bmod2}(1-s^2)^{\lfloor j/2\rfloor}}
\right].
$$

In order, its values for $t=0,1,2,3,4$ give Conjectures 26–30.

| $t$ | $\bar T_t(z,5)$ |
|---:|---|
| 0 | $1/(1-s)$ |
| 1 | $s^2/[(1+s)(1-s)^2]$ |
| 2 | $s^3/[(1+s)(1-s)^3]$ |
| 3 | $s^4(1+s^2)/[(1+s)^2(1-s)^4]$ |
| 4 | $s^5(1+s^2)/[(1+s)^2(1-s)^5]$ |

At height 7 the three letters record the position of the height-3 band. Top-to-bottom reflection exchanges the two outside positions and fixes the middle one. All three blocks are invariant under left-to-right reflection, which reverses the word. The identity fixes all words, with generating function $1/(1-3s)$. The top-to-bottom reflection fixes words of the middle letter, with function $1/(1-s)$. For reversal and for reversal followed by the letter exchange, the left half is arbitrary. A middle letter has respectively three choices or one fixed choice. Averaging the four counts proves Conjecture 34,

$$
\bar T(z,7)=\frac14\left(
\frac1{1-3s}+\frac1{1-s}+
\frac{1+3s}{1-3s^2}+\frac{1+s}{1-3s^2}\right)
=\frac{1-2s-4s^2+6s^3}{(1-s)(1-3s)(1-3s^2)}.
$$

The square boards of sides 5 and 7 admit no tilings because their areas are not multiples of 6. No square correction enters either word count.

## Independent exact check at height eight

The [Python verifier](verify.py) obtains the eight-row functions directly from column states. Each state lists the height of every tile in the column and its remaining width including that column. Each tile with remaining width above one continues in the same rows of the next column. All gaps are filled by new tiles. An interior row break is a four-tile meeting precisely when it appears on both sides of the seam and both old tiles adjacent to it end there. A tiling ends exactly when all remaining widths equal one. Thus paths from the empty start state to an accepting state count the required tilings bijectively.

Both graphs have 34 reachable states. The unrestricted graph has 57 transitions and its tatami subgraph has 37. If $M$ is the adjacency matrix, the coefficient sequence is $f_n=uM^nv$ for the initial row vector $u$ and the vector $v$ indicating accepting states. To certify $F=P/Q$, let $d=\deg Q$ and $N=\max(d,1+\deg P)$. For $n\ge N$ the residual coefficient $[z^n](QF-P)$ has the form $uM^{n-d}(\sum_{i=0}^d Q_iM^{d-i})v$ and satisfies the characteristic recurrence of $M$. Checking the residual from $0$ through $N+33$ suffices by Cayley–Hamilton. The script does so in exact integer arithmetic, through widths 45 and 52 respectively. Run it with Python 3.

## Earlier work

Mathar states the six-row composition model in the 2013 paper and derives ordinary tiling functions by transfer matrices in 2014, including the corrected eight-row function. Aggarwal and Ram's 2022 results concern straight $1\times k$ tiles. The arguments above concern rectangular $2\times3$ tiles and include their four-corner and symmetry refinements. [Mathar (2013), §5](https://arxiv.org/html/1311.6135v1#S5) · [Mathar (2014), §3](https://arxiv.org/pdf/1406.7788) · [Aggarwal and Ram (2022)](https://arxiv.org/abs/2206.04437)
