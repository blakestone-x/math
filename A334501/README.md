# Exact periods of five elementary cellular automata on a ring

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Start an $n$-cell binary ring with one ON cell at position zero. Let $p_R(n)$ be the least eventual period of its configuration under elementary rule $R$. This is the statistic computed by Bradley Klee's program in the related entry A334496 and by the program in A334509. The bit of $R$ at position $4a+2b+c$, counted from the low bit, is the new value of the cell with left, center and right neighbor values $(a,b,c)$. [OEIS A334496](https://oeis.org/A334496) · [OEIS A334509](https://oeis.org/A334509)

**Theorem.** The following formulas and exceptional prefixes give all positive widths.

| Rule | OEIS | Formula | Range | Earlier values in order, starting at $n=1$ |
|---:|---|---|---:|---|
| 9 | [A334511](https://oeis.org/A334511) | $2n/\gcd(2,n)$ | $n\ge11$ | 2, 2, 2, 2, 2, 9, 5, 12, 18, 5 |
| 25 | [A334513](https://oeis.org/A334513) | $2n$ | $n\ge10$ | 2, 2, 3, 2, 15, 15, 21, 16, 9 |
| 41 | [A334509](https://oeis.org/A334509) | $4n/\gcd(4,n)$ | $n\ge7$ | 2, 2, 2, 2, 15, 2 |
| 107 | [A334514](https://oeis.org/A334514) | $4n/\gcd(4,n)$ | $n\ge17$ | 2, 2, 3, 2, 15, 2, 28, 2, 36, 20, 11, 12, 117, 28, 60, 8 |
| 190 | [A334501](https://oeis.org/A334501) | $4$ if $4\mid n$, otherwise $n$ | $n\ge4$ | 1, 1, 1 |

These prove the conjectured size formulas of Stefano Spezia for rules 9 and 41 and Václav Kotěšovec for rule 25. They also give all five rational generating functions proposed by Colin Barker. One proposed recurrence has two exceptions inside its stated range, at widths 10 and 11 for rule 190.

The whole-ring convention matters at width eight for rule 107. Its eventual states are $01110111$ and $11011101$, written with the initially ON site on the right. That site stays ON in both, while the ring has the period two listed by OEIS. On the infinite line, Brummitt and Rowland previously described the four-phase boundary of rule 107, and the single-seed pattern of rule 190 is also recorded in the literature. [Brummitt and Rowland, Figure 2](https://doi.org/10.25088/ComplexSystems.21.2.85) · [Weisstein, *Rule 190*](https://mathworld.wolfram.com/Rule190.html)

## Four translating patterns

First work on the infinite line. For each of rules 9, 25, 41 and 107, a uniform zero background switches to ones after one step, and back to zeros after two. At time $t$ record the sites that differ from this background. In the following table each entry gives the position of the leftmost such site followed by a binary word marking the defects. Coordinates increase to the right. Each column stops as soon as an earlier phase returns translated.

| $t$ | Rule 9 | Rule 25 | Rule 41 | Rule 107 |
|---:|---|---|---|---|
| 0 | 0, 1 | 0, 1 | 0, 1 | 0, 1 |
| 1 | −1, 111 | −1, 11 | −1, 111 | 0, 11 |
| 2 | 0, 101 | −1, 101 | 0, 101 | −1, 1011 |
| 3 | −1, 11111 | −2, 1111 | −1, 11011 | −1, 10001 |
| 4 | 0, 11101 | −2, 11101 | 4, 1 | −2, 1110111 |
| 5 | −1, 1011111 | −3, 101111 | | −1, 1000101 |
| 6 | 2, 11101 | −1, 11101 | | −2, 111011011 |
| 7 | | | | −1, 100000001 |
| 8 | | | | −2, 11100000111 |
| 9 | | | | −1, 10100000101 |
| 10 | | | | −2, 1101100011011 |
| 11 | | | | 3, 100000001 |

Every row follows by evaluating the eight-entry local rule on the preceding row, padding with the current background. For example, rule 41 after four steps has returned to a single ON cell four places to the right. No defect word in the table spans more than 13 sites. To make each update it suffices to enlarge its interval by one at each end. For $n\ge17$ these enlarged intervals around the periodic copies are disjoint. Induction therefore gives the same table on the ring, with positions read modulo $n$. Since translation commutes with the update, each translation identified in the table continues for all future time.

Let $t_0$ be the indicated starting phase, $d$ the number of steps until its translated return, and $s$ the translation. The numbers of ON cells, in order during those $d$ steps, are as follows.

| Rule | $t_0$ | $d$ | $s$ | ON counts for phases $0,\ldots,d-1$ |
|---:|---:|---:|---:|---|
| 9 | 4 | 2 | 2 | $4,\ n-6$ |
| 25 | 4 | 2 | 1 | $4,\ n-5$ |
| 41 | 0 | 4 | 4 | $1,\ n-3,\ 2,\ n-4$ |
| 107 | 7 | 4 | 4 | $n-2,\ 6,\ n-4,\ 8$ |

For $n\ge17$ the counts within each row are distinct. Any return to the configuration at $t_0$ takes a multiple of $d$ steps. Its defect set at $t_0$ has no nonzero rotational symmetry. For rules 9 and 25 the word $11101$ has a unique longest circular gap between successive defects. For rule 41 there is a single defect. For rule 107 the two defects have circular gaps 8 and $n-8$, which differ at all these widths. Thus after $kd$ steps the initial phase returns exactly when $ks\equiv0\pmod n$. Its least period is $dn/\gcd(s,n)$ as claimed.

For the four rules the remaining widths $1\le n\le16$ are a finite check using the stated truth tables. Start at the integer $1$, encoding a ring by its $n$ low bits. Store the current time on the first visit to each state, compute the next state simultaneously around the ring, and stop at the first repeated state. The difference of its two visit times is the period of the cycle. The Python verifier implements this enumeration. An independent Lean certificate runs the local rule site by site and checks the first return from time 16 for each of the five rules at all sixteen small widths. [Finite case enumeration and template checks](verify.py) · [Lean certificate](SmallRings.lean)

## Rule 190

Rule 190 outputs zero precisely on neighborhoods $000$ and $110$. On the infinite line, at time $t$ all sites outside $[-t,t]$ are zero, and on this interval the configuration is the length-$2t+1$ prefix of the repeated word $1110$. To see the induction, measure the new site's offset $j$ from the new left end. Its old three-site neighborhood has offsets $j-2,j-1,j$ from the old left end. In the repeated word it gives zero exactly at $j\equiv3\pmod4$. At the left edge the first two new sites are ones. If the old length $L$ is $1\bmod4$, its last one is preceded by a zero (the outside zero when $L=1$), and the two new right-edge entries at $L,L+1$ are $11$. If $L$ is $3\bmod4$ the last two old sites are ones and these new entries are $01$. This proves the prefix assertion, including the boundary. Until the enlarged interval first fills the ring, its periodic copies give the same updates.

In any ring configuration with isolated zeros, a zero produces a zero one place to its left exactly when both sites preceding it are ones. In particular, once all circular gaps between zeros are at least three, the entire pattern translates left by one each step. Its temporal period is then its least spatial period.

- For odd $n\ge5$, at $t=(n-1)/2$ the prefix fills the ring. If $n=4q+1$, the circular gaps between zeros are fours and one five. If $n=4q+3$, they are fours and one seven. The exceptional gap distinguishes an individual zero, so the spatial period is $n$. This also works when there is just one zero.
- For $n=4q$, at $t=n/2-1$ the prefix has length $n-1$. The remaining outside zero completes $(1110)^q$. Its least period is four.
- For $n=4q+2\ge6$, at $t=n/2-1$ the ring consists of $(1110)^q10$. All zeros are isolated. The final zero is the only one with its preceding zero two places away. The next update shifts every other zero left and removes this one. The resulting gaps are fours and one six, so the period is $n$.

At widths $1,2,3$ the ring becomes or starts all ones and is fixed. This completes the five period proofs. ∎

## The generating functions and the recurrence correction

Extend $p_R(n)$ by zero at $n\le0$. For rules $9,25,41,107,190$ take $h=2,1,4,4,4$, respectively. In their stated ranges the period formulas are affine functions of $n$ on each residue class modulo $h$. Thus the numerator of the ordinary generating function with denominator $(1-x^h)^2$ has coefficient

$$
p_R(n)-2p_R(n-h)+p_R(n-2h)
$$

at $x^n$. Substitution of the finite prefixes gives Barker's five listed numerators. Their final nonzero terms are $-5x^{14},-9x^{11},-10x^{14},-8x^{24},-2x^{11}$ in the same rule order. The verifier checks every coefficient against the entries.

For rule 190, Barker's stated recurrence starts at $n>8$. At $n=10$ it predicts $2\cdot6-1=11$ where the period is 10. At $n=11$ it predicts $2\cdot7-1=13$ where the period is 11. It holds at $n=9$ and at every $n\ge12$. The generating function as printed is correct. [OEIS A334501](https://oeis.org/A334501)
