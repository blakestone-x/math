# Symmetry classes of three-row domino tilings

Blake Stone · Proof developed with OpenAI Codex.

Let $a_n$ count the tilings of a $3\times 2n$ rectangle by dominoes, identifying tilings related by a symmetry of the board. Take $a_0=1$. The generating function was Richard J. Mathar's Conjecture 6, equation (26). The same formula and an equivalent recurrence appear in OEIS A232622. [Mathar, 2013](https://arxiv.org/html/1311.6135v1) · [A232622](https://oeis.org/A232622)

**Earlier proof.** Shiqi Liu's October 2026 preprint proves both the generating function and Alcover's recurrence. Liu gives two proofs, including a decomposition into blocks with the same reflection and palindrome count used below. This note gives a short self-contained exposition of that argument. The [companion note](bar-crossings.md) concerns a different statistic, the number of four-tile intersections for bars whose length equals the strip height. [Liu, *Domino tilings of odd-height rectangles up to symmetry*, v2.1](https://github.com/Lshiqi67/domino-tilings-a232622/releases/tag/paper-en-v2.1)

The [three-row crossing proof](three-row-crossings.md) derives the exact formulas for one or two four-domino meetings on a fixed board. It corrects equation (16) and confirms equation (17) in Mathar's paper.

## Theorem

The ordinary generating function $G(x)=\sum_{n\ge0}a_nx^n$ is

$$
G(x)=\frac{1-3x-4x^2+10x^3-4x^5+x^6}
{(1-x)(1-4x+x^2)(1-4x^2+x^4)}.
$$

Consequently, for $n\ge7$,

$$
a_n=5a_{n-1}-a_{n-2}-19a_{n-3}+19a_{n-4}
      +a_{n-5}-5a_{n-6}+a_{n-7},
$$

with initial terms $1,2,5,14,46,156,561$. This is Jean-François Alcover's recurrence in A232622.

## A word for each tiling

Cut the board at every vertical gridline crossed by no domino. A tiling becomes a unique ordered list of blocks. The block widths are even. In units of two columns, the block alphabet has one letter $U$ of weight one, and two letters $A_k,B_k$ of each weight $k\ge1$.

Indeed, if the leftmost column contains no vertical domino, all three horizontal dominoes extend into the second column and finish the block. This is $U$. Otherwise, a vertical domino fills the upper or lower two cells of the first column. The remaining row starts a horizontal domino. In the next column, the two free cells can be closed by a vertical domino, ending the block. The alternative is to start two horizontal dominoes in those cells. The following column then forces a horizontal domino in the remaining row, returning to the same two-free-cell choice two columns farther along. Thus for each width $2k$ there is exactly one block beginning with each of the two possible vertical dominoes. The construction ends with a vertical domino in the same two rows as the first.

Each block is symmetric under left-right reflection. This follows also by reflecting it: its width and starting vertical pair uniquely determine the block, and the exception $U$ is itself symmetric. Top-bottom reflection interchanges $A_k$ and $B_k$ for each $k$ and fixes $U$. This block decomposition for unrestricted three-row tilings is classical. [Ardila, *Algebraic and geometric methods in enumerative combinatorics*, Example 6 in the generating functions discussion](https://www-users.cse.umn.edu/~reiner/Classes/Ardila_handbook_chapter.pdf)

Let

$$
I(x)=x+\frac{2x}{1-x},\qquad
F(x)=\frac1{1-I(x)}=\frac{1-x}{1-4x+x^2}.
$$

Here $I$ counts letters and $F$ counts arbitrary words, including the empty word.

## Count the fixed words

For $n\ge1$ the board is a nonsquare rectangle, with four symmetries. The empty tiling contributes one under each action as well.

| Symmetry | Fixed words | Generating function |
|---|---|---|
| Identity | Arbitrary words | $F(x)$ |
| Top-bottom reflection | Only repetitions of $U$ | $1/(1-x)$ |
| Left-right reflection | Palindromes | $(1+I(x))F(x^2)$ |
| Half-turn | A word equals its reversal after interchanging $A_k$ and $B_k$ | $(1+x)F(x^2)$ |

For either reversal, the first half of the word determines the last half. Each letter in the first half contributes twice its weight, giving $F(x^2)$. A palindrome permits any central letter or none. For the half-turn, the only possible central letter is $U$.

Burnside's lemma averages these four series. In particular

$$
G(x)=\frac1{4(1-x)}
     +\frac{1+2x-x^3}{2(1-4x^2+x^4)}
     +\frac{1-x}{4(1-4x+x^2)}.
$$

With $x=z^2$, this is exactly Mathar's equation (26), where $z$ marks one column. Putting the three terms over a common denominator gives the theorem. Multiplying by that denominator and comparing coefficients gives the recurrence. The [symbolic checks](verify.py) reproduce these identities.
