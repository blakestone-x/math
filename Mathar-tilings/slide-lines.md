# Counting tilings by horizontal slide lines

**Blake Stone · Proof developed with OpenAI Codex.**

A horizontal slide line runs between two adjacent rows across the full length of a tiled board without intersecting the interior of a tile. We prove Conjectures 35–44 in Richard J. Mathar's *Paving Rectangular Regions with Rectangular Tiles*. Conjectures 35–39 and 42–44 count placements on a fixed board. Conjectures 40–41 identify placements under the symmetries of a three-row rectangle. We keep the row orientation used in the paper's tables, including when the width is small. Generating functions use $z$ for one column. The empty board contributes one tiling with zero lines. [Mathar, §§1.3 and 6](https://arxiv.org/html/1311.6135v1)

## Counting specified lines

At positive width $n$ let $D_h(n)$ denote the total number of tilings of an $h$-row strip by the tile in question. Specifying $j$ distinct horizontal lines cuts the board into $j+1$ ordered strips. Tilings of these strips can be chosen independently. Thus the number of tilings together with $j$ distinguished slide lines is

$$
B_j(n,h)=\sum_{\substack{h_1+\cdots+h_{j+1}=h\\h_i\ge1}}
                    \prod_{i=1}^{j+1}D_{h_i}(n).
$$

A tiling with exactly $r$ lines is counted $\binom rj$ times. Consequently the polynomial counting tilings by their exact number of lines is $\sum_j B_j(n,h)(y-1)^j$. This is the strip decomposition used in Mathar's §6, expressed with marked lines to track every multiplicity. Mathar's later fault enumeration also tabulates counts with and without horizontal faults. [Mathar, §6.1](https://arxiv.org/html/1311.6135v1#S6.SS1) · [*Fault-free Tilings with Dominoes or Trominoes* (2022)](https://oeis.org/A046984/a046984.pdf)

## Dominoes on a fixed board, Conjectures 35–39

Put $e=[2\mid n]$ and $d=F_{n+1}$, with $F_0=0,F_1=1$. Then $D_1(n)=e$ and $D_2(n)=d$, since the first block in a two-row strip is one vertical domino or two horizontal dominoes. Let $a=D_3(n)$ and $b=D_4(n)$. The marked-line counts at heights three and four are

| Height | $B_0$ | $B_1$ | $B_2$ | $B_3$ |
|---|---:|---:|---:|---:|
| 3 | $a$ | $2ed$ | $e$ | $0$ |
| 4 | $b$ | $2a+d^2$ | $3ed$ | $e$ |

Here $ea=a$ because an odd-width three-row board has odd area. For positive widths, expanding the marking polynomial gives the following exact counts.

| Height | 0 lines | 1 line | 2 lines | 3 lines |
|---|---:|---:|---:|---:|
| 3 | $a-2ed+e$ | $2ed-2e$ | $e$ | $0$ |
| 4 | $b-2a-d^2+3ed-e$ | $2a+d^2-6ed+3e$ | $3ed-3e$ | $e$ |

For completeness, setting $x=z^2$, the ordinary generating functions over $n\ge0$ of the table's ingredients are

| Sequence | Generating function |
|---|---|
| $e$ | $1/(1-x)$ |
| $ed$ | $(1-x)/(1-3x+x^2)$ |
| $d^2$ | $(1-z)/((1+z)(1-3z+z^2))$ |
| $a$ | $(1-x)/(1-4x+x^2)$ |
| $b$ | $(1-x)/(1-z-5z^2-z^3+z^4)$ |

The two Fibonacci entries follow from the Fibonacci recurrence. For example the even subsequence $1,2,5,\ldots$ satisfies $s_{j+2}=3s_{j+1}-s_j$. The squares $1,1,4,\ldots$ satisfy $s_{n+3}=2s_{n+2}+2s_{n+1}-s_n$, as follows by expanding $F_{n+2}=F_{n+1}+F_n$. The last two series are the classical total counts quoted as Theorems 2 and 4 of the paper. Substitute into the exact counts, assigning the width-zero contribution to the zero-line class. This gives equations (61)–(65). [Mathar, §2.1](https://arxiv.org/html/1311.6135v1#S2.SS1)

## Three rows up to symmetry, Conjectures 40–41

Positive widths must be even, say $n=2j$. With exactly one slide line there is a unique isolated outside row. Reflect top to bottom if necessary to place that row at the top. It is tiled uniquely. In the remaining two rows choose any domino tiling other than the entirely horizontal one. The only remaining identification is left-right reflection, which reverses the word of blocks of lengths 1 and 2.

There are $F_{2j+1}$ such words before removing the all-horizontal word. The number of palindromic words of weight $2j$ is $F_{j+1}+F_j$. In fact the center is either empty (choose any half-word of weight $j$) or a single length-two letter (half-word of weight $j-1$). For $j=0$ only the empty word occurs. Reversal orbits therefore give $(F_{2j+1}+F_{j+1}+F_j)/2-1$ one-line classes. The subtracted all-horizontal word is itself fixed by reversal.

Their generating function, with $x=z^2$, is

$$
H=\frac12\left(\frac{1-x}{1-3x+x^2}+\frac{1+x}{1-x-x^2}\right)-\frac1{1-x}
=\frac{x(1-2x)}{(1-x)(1-3x+x^2)(1-x-x^2)}.
$$

This proves (68). The two-line class is unique at each positive even width and has series $x/(1-x)$. The zero-line series is therefore the total orbit series minus $H+x/(1-x)$, giving (69). The total orbit series (26) has a prior proof by Shiqi Liu. [Liu, *Domino Tilings of Odd-Height Rectangles up to Symmetry*](https://github.com/Lshiqi67/domino-tilings-a232622) · [Short exposition](../A232622/README.md)

## Straight trominoes, Conjectures 42–44

On a three-row board the leftmost block is a vertical bar of width one, or a stack of three horizontal bars of width three. The total generating function is $1/(1-z-z^3)$. A single vertical bar crosses both horizontal interfaces. The only positive-width tilings with slide lines have no vertical bar and have two lines, one tiling at each multiple of three. Subtracting $z^3/(1-z^3)$ leaves the zero-line series (70). Mathar already pointed to the associated sequence A099560. [OEIS A099560](https://oeis.org/A099560)

On a four-row board every admissible width is divisible by three. A middle slide line splits the board into two strips of height two, both necessarily all-horizontal. Two slide lines likewise leave strips of heights at most two, so there are then three lines. For exactly one line, choose the top or bottom outside row, then tile the remaining three rows with at least one vertical tromino.

Put $t=z^3$. The series counting three-row tilings at widths divisible by three is

$$
M=\frac{1}{1-t}\sum_{j\ge0}\left(\frac{t}{(1-t)^3}\right)^j
=\frac{(1-t)^2}{1-4t+3t^2-t^3}.
$$

Indeed the number of vertical bars must be $3j$, and the $3j+1$ gaps around them accept arbitrary runs of width-three blocks. Consequently the one-line series on the four-row board is $2(M-1/(1-t))$, which gives (71). The three-line series is $t/(1-t)$ and the two-line series is zero. Subtracting these series from the total $(1-t)^2/(1-5t+3t^2-t^3)$ gives the zero-line series (72). The total is Theorem 14 in the paper. [Mathar, §3.1](https://arxiv.org/html/1311.6135v1#S3.SS1)

The [exact algebra check](verify-slide-lines.py) clears the denominators of the derived and printed rational functions for each of the ten statements. The combinatorial arguments establish that the derived functions enumerate all widths.
