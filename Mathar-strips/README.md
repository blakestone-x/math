# Four-tile junctions in narrow strips tiled by straight bars

**Blake Stone · Proof developed with OpenAI Codex.**

Tile an $m\times n$ board with $1\times k$ rectangles, allowing both orientations and counting each placement on the fixed board. A **junction** is an interior grid vertex where four distinct tiles meet. A tiling with no junctions is called a tatami tiling. We count junctions for every $k<m<2k$. The zero-junction case proves Conjectures 8 and 16 of Richard J. Mathar about three-cell and four-cell bars. [Mathar, 2013, equations (32) and (40)](https://arxiv.org/html/1311.6135v1)

The proof uses the classification of blocks between vertical faults given by Mudit Aggarwal and Samrith Ram. Their Theorem 8 already counts unrestricted tilings on all of these boards. We give the block argument here to determine where junctions occur, both within a block and along its boundary. [Aggarwal and Ram, *Journal of Integer Sequences* 26 (2023), Article 23.1.4, Lemma 4 and Proposition 5](https://cs.uwaterloo.ca/journals/JIS/VOL26/Ram/ram3.pdf)

## The zero-junction count

Put $t=m-k$ and $x=z^k$, where $z$ normally marks a single column. Every tileable width is a multiple of $k$, so $x$ records sets of $k$ columns. The empty board contributes one. The generating function for tatami tilings is

$$
\begin{cases}
\displaystyle -1+x+\frac{2}{1-x(1+x)^{k-1}},&t=1,\\[6pt]
\displaystyle 1+4x+\frac{2x^2}{1-x}+x\big((1+x)^{k-1}-1\big),&t=2,\\[6pt]
\displaystyle 1+(t+2)x+\frac{2x^2}{1-x},&3\le t<k.
\end{cases}
$$

The first line at $k=3$ and $4$ gives Mathar's Conjectures 8 and 16 respectively. The denominators in the fractional term are $1-z^3-2z^6-z^9$ and $1-z^4-3z^8-3z^{12}-z^{16}$. For $t=2$, a width $k\ell$ with $\ell\ge2$ admits $2+\binom{k-1}{\ell-1}$ tatami tilings, where the binomial is zero when $\ell>k$. For $3\le t<k$, every width $k\ell$ with $\ell\ge2$ admits exactly two.

## The blocks and their junctions

Cut at every internal vertical gridline crossed by no tile. These cuts split any tiling uniquely into blocks. One type, $U$, is a single stack of $m$ horizontal bars and has width $k$. Every other block has a band of $k$ consecutive rows containing all its vertical bars. Let $s$ denote the number of rows above the band, with $0\le s\le t$. The other $t-s$ exterior rows lie below it.

Here is a proof of the classification. A block beginning with an entirely horizontal column is $U$, since all bars in that column end together. Otherwise its first column has a vertical bar across a band of $k$ rows. Before any vertical bar changes band, the rows outside the initial band consist of horizontal bars aligned to the left edge. Inside the band, the vertical bars occupy all $k$ rows at once, and the intervening horizontal bars start and end together. A first bar in a different band would occupy both an exterior row and an original band row, since $m<2k$. At its left edge an exterior row must therefore be free, making every exterior row free. Likewise one free band row makes every band row free. This gridline would be an internal cut, contradicting the definition of a block.

There is at least one exterior row, so a block of type $s$ has width a multiple of $k$. In its band write $V$ for one vertical bar and $H$ for a stack of $k$ horizontal bars. Its word starts and ends with $V$ (apply the first-column argument from either end). Its number of $V$'s is divisible by $k$. Immediately after its $k$-th $V$, the used width is a multiple of $k$, so the band and every exterior row end a tile there. Thus this is the end of the block. Conversely, any word of precisely $k$ letters $V$, beginning and ending with $V$, with any number of $H$'s in the $k-1$ gaps, gives such a block. A proper word boundary has encountered between one and $k-1$ letters $V$, so it cannot line up with an exterior boundary. If $j$ letters $H$ are used, the width is $k(1+j)$.

The following rules count every junction.

* **Inside the band.** Each adjacent $HH$ contributes $k-1$ junctions. A boundary involving $V$ contributes none inside the band.
* **Outside the band.** Each of the $j$ interior multiples of $k$ contributes $E_s=\max(s-1,0)+\max(t-s-1,0)$ junctions between adjacent exterior rows. At either interface between the band and exterior rows a junction would require a band boundary at the same multiple of $k$, which would be an internal cut. The block $U$ has no internal junctions.
* **At a cut.** On either end of a block of type $s$, the row boundaries separating distinct tiles form the set $\{1,\ldots,s\}\cup\{s+k,\ldots,m-1\}$, numbering from the top. If consecutive blocks have types $s,r$, their common row boundaries give $t-|s-r|$ junctions. A $U$ beside a block of type $s$ gives $t$ junctions. Two $U$'s give $m-1$.

## Counting the junction-free words

In a junction-free tiling, a $U$ must stand alone. Otherwise, two successive blocks must have $|s-r|=t$ and hence must alternate between $0$ and $t$. Within any single block its band has at most one $H$ in each gap.

If $t=1$, both types have $E_s=0$. A block of either prescribed type has generating function $C=x(1+x)^{k-1}$, since each of its $k-1$ gaps can independently contain one $H$. A nonempty sequence of these blocks allows two choices for its first orientation, then alternates. The total is $1+x+2C/(1-C)$, giving the first formula.

If $t\ge2$, an extreme block of type $0$ or $t$ has $E_s>0$. It must therefore have width $k$. At every width $k\ell$ for $\ell\ge2$, the two alternating lists of $\ell$ such blocks give two solutions. A single block of width $k$ can be $U$ or any of the $t+1$ orientations. For a wider single block we must have $E_s=0$, meaning $s\le1$ and $t-s\le1$. This happens only at $t=2,s=1$. Choosing $\ell-1$ of the $k-1$ gaps for $H$ gives the extra binomial term, completing the proof.

## Counting every junction number

Let $q$ mark individual junctions. The weight of the block $U$ is $w_U=x$. The series for blocks of a prescribed orientation $s$ is

$$
w_s=x\left(1+\frac{xq^{E_s}}{1-xq^{E_s+k-1}}\right)^{k-1}.
$$

Indeed, a gap with $g\ge1$ copies of $H$ adds $gE_s+(g-1)(k-1)$ junctions and weight $x^g$. The $k-1$ gaps may be filled independently.

Index a matrix $M$ by $U,0,\ldots,t$. Let $c(a,b)$ be the number of junctions at the cut between block types $a,b$, as given above. Put $M_{a,b}=q^{c(a,b)}w_b$ and let $\mathbf w$ be the row of initial weights. Then the full generating function is

$$
1+\mathbf w(I-M)^{-1}\mathbf 1.
$$

The coefficient of $x^\ell q^j$ counts tilings of width $k\ell$ with $j$ junctions. The inverse exists as a formal power series since $M$ has zero constant term in $x$. Its geometric expansion enumerates block sequences. Each tile lies in exactly one block and every junction has been counted once.

At $q=1$ the expression reduces to $(1-x)^{k-1}/((1-x)^k-(t+1)x)$, precisely Aggarwal and Ram's unrestricted formula. In particular Mathar's Conjectures 9, 15, 17 and 18 already follow from their theorem. Mathar himself derived these four special cases in 2014 by transfer matrices, in equations (12), (24), (26) and (27) respectively, using a variable that marks individual tiles. In Conjecture 9, Table 20 is for height five although equation (33) prints height three. In Conjecture 18, combining the two fractions in (42) gives the same formula at $(k,m)=(4,7)$. The fixed-height tatami domino case $k=2$ also has earlier treatments. [Mathar, *Counts Derived from Transfer Matrices*](https://arxiv.org/pdf/1406.7788) · [Aggarwal and Ram, Theorem 8](https://cs.uwaterloo.ca/journals/JIS/VOL26/Ram/ram3.pdf) · [Ruskey and Woodcock, *Counting fixed-height tatami tilings*](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v16i1r126)

The [verification program](verify.py) independently tiles finite boards cell by cell and checks the complete distribution of junction counts against the block formula.
