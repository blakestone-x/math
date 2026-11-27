# Two strict containments for ordinary and carryless binary products

**Blake Stone · Proof developed with OpenAI Codex.**

Let $C(p,n)$ be the carryless binary product, computed by XORing copies of $n$ shifted by the one-bit positions of $p$. Consider the sets of nonnegative integers

$$
A=\{n:15n=C(23,n)\},\qquad B=\{n:13n=C(21,n)\},\qquad D=\{x\mathbin{\mathrm{OR}}4x:x\ge0\}.
$$

The entries A115774 and A115772 ask whether $A\subseteq B$. A115772 also records Gary Detlefs's 2010 suggestion that $B=D$. The same comparison is raised in A178891. [A115774](https://oeis.org/A115774) · [A115772](https://oeis.org/A115772) · [A178891](https://oeis.org/A178891)

**Theorem.** The proper inclusions $A\subsetneq B\subsetneq D$ both hold. In particular, $325=65\mathbin{\mathrm{OR}}260$ belongs to $D$, while $13\cdot325=4225$ and $C(21,325)=4097$.

## A bit-by-bit description of the two larger sets

Split the bits of an integer into two tracks, the bits in even positions and the bits in odd positions. Pad each track with zeros in both directions. A bit is *isolated* if both neighbors on its track differ from it.

**Claim.** Membership in $D$ means that neither track has an isolated one. Membership in $B$ means that neither track has any isolated bit.

For $D$, each one in $x$ places two adjacent ones on its track in $x\mathbin{\mathrm{OR}}4x$. Conversely, each run of at least two ones is a union of adjacent pairs. Choose, for $x$, the lower bit of each such adjacent pair in the runs of a proposed output. These pairs cover exactly the proposed support.

For $B$, the following identity holds for all nonnegative integers $u,v,w$, with $M$ their bitwise majority (a one where at least two inputs have a one):

$$
u+v+w=(u\mathbin{\oplus}v\mathbin{\oplus}w)+2M.
$$

This follows by adding the three bits in each position as integers and then summing with their positional weights. Take $(u,v,w)=(n,4n,16n)$. The left side is $21n$, and the XOR on the right is $C(21,n)$. Thus $13n=C(21,n)$ holds exactly when $M=4n$. At every position, this means the middle of three adjacent bits on one track equals their majority. This is equivalent to forbidding isolated bits on that track. Triples centered at negative positions contain no isolated bit under the zero padding. This proves the claim and $B\subseteq D$.

At $n=325$ the occupied positions are $0,2,6,8$. Its even track has runs $11,0,11$, which include an isolated zero. The displayed counterexample proves $B\subsetneq D$. Shifting $325$ to the left any number of places gives further counterexamples.

## A finite induction for the smaller set

For constants $p,q$, encode a remaining-input predicate by the state $(c,m)$, meaning

$$
pt+c=C(q,t)\mathbin{\oplus}m.
$$

State $(0,0)$ tests membership. For an input $t=2s+b$ with $b=0$ or $1$, put $v=c+pb$ and $w=m\mathbin{\oplus}(qb)$. If their low bits differ the predicate fails. Otherwise it reduces to the same predicate at input $s$ with state $(\lfloor v/2\rfloor,\lfloor w/2\rfloor)$. This follows from $C(q,2s+b)=2C(q,s)\mathbin{\oplus}(qb)$. At input zero the test is simply $c=m$.

The table starts at row 0, pairing the state for $(p,q)=(15,23)$ on the left with that for $(13,21)$ on the right. An entry in a bit column is the row after consuming that bit. A dash means the left predicate already failed. All entries follow directly from the update above.

| Row | Left state | Right state | Bit 0 | Bit 1 |
|---:|:---:|:---:|---:|---:|
| 0 | (0, 0) | (0, 0) | 0 | 1 |
| 1 | (7, 11) | (6, 10) | 2 | 3 |
| 2 | (3, 5) | (3, 5) | 4 | 5 |
| 3 | (11, 14) | (9, 15) | – | – |
| 4 | (1, 2) | (1, 2) | – | – |
| 5 | (9, 9) | (8, 8) | 6 | 7 |
| 6 | (4, 4) | (4, 4) | 8 | 5 |
| 7 | (12, 15) | (10, 14) | – | – |
| 8 | (2, 2) | (2, 2) | 9 | 10 |
| 9 | (1, 1) | (1, 1) | 0 | 11 |
| 10 | (8, 10) | (7, 11) | 12 | 13 |
| 11 | (8, 11) | (7, 10) | – | – |
| 12 | (4, 5) | (3, 5) | – | – |
| 13 | (11, 14) | (10, 15) | – | – |

In each row where the two coordinates of the left state agree, the two coordinates of the right state agree as well. Thus the implication holds at remaining input zero for every row. Induction on the remaining input proves it at every row: on input $2s+b>0$, either the left predicate fails immediately, or the indicated row gives the implication at the smaller input $s$. Row 0 yields $A\subseteq B$ for every integer. For strictness take $n=15$: $13n=C(21,n)=195$, whereas $15n=225$ and $C(23,n)=221$.

The accompanying Python program reconstructs the entire transition table from the two multiplier pairs. The induction uses this finite table for inputs of arbitrary length. [Certificate checker](verify.py)

## Other strides

The majority argument applies verbatim at stride $h\ge1$. Set $t=2^h$. Then $(1-t+t^2)n=C(1+t+t^2,n)$ holds exactly when none of the $h$ tracks of bit positions modulo $h$ has an isolated bit. The range of $x\mapsto x\mathbin{\mathrm{OR}}tx$ instead forbids just isolated ones. For every stride the inclusion is strict: choose the single occupied track to have occupied indices $0,1,3,4$ in that track.
