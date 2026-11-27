# A288523: the replacement-length conjecture

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

Start from $w_0=00$, and scan each word from left to right, making the nonoverlapping replacements

$$
00\longmapsto0101,\qquad10\longmapsto010.
$$

Copy any letter which does not start a matching pair. This is the literal operation in [A288520](https://oeis.org/A288520). We prove the conjectured equality of its lengths with [A288523](https://oeis.org/A288523) for **every** index. The repeated assertion in the two entries is counted once.

Writing $L_n=|w_n|$, the result is

$$
\boxed{L_N=L_{N-1}+L_{N-2}+L_{N-3}-2L_{N-4}\qquad(N\ge5),}
$$

with the exact initial values

$$
(L_0,L_1,L_2,L_3,L_4)=(2,4,5,8,11).
$$

The proof also gives the shorter affine recurrence

$$
\boxed{L_{n+3}+2=L_{n+1}+2L_n\qquad(n\ge1).}
$$

The recurrence starts after the initial word, as specified. In particular, the order-four formula is not asserted at $N=4$, where it fails.

## Exact coding of the literal scanner

Introduce tokens with binary codes

$$
A=01,\qquad B=001,\qquad C=0001,
$$

and the token substitution

$$
h(A)=B,\qquad h(B)=C,\qquad h(C)=BAA.
$$

For a token word $v$, let $d(v)$ denote its decoded binary word. There are two boundary states:

$$
E_0(v)=01\,d(v)\,01,
\qquad
E_1(v)=001\,d(v)\,01.
$$

Let $R$ be one literal replacement pass. The decisive identity, valid for **every finite token word** $v$, is

$$
R(1\,d(v)\,01)=01\,d(h(v))\,01. \tag{1}
$$

For the empty token word, this is $R(101)=0101$. For a leading token $A$, $B$, or $C$, the scanner consumes the initial bits up to the next leading $1$ and emits respectively

$$
010,\qquad0100,\qquad0100101.
$$

The remaining scan has the form on the left of (1). The three boundary equalities are

$$
\begin{aligned}
010\,01&=01\,001,\\
0100\,01&=01\,0001,\\
0100101\,01&=01\,0010101.
\end{aligned}
$$

These prove (1) by induction on $v$. Thus this is an exact scanner identity, not an assumption that rewriting preserves arbitrary binary concatenations.

Applying (1) to the two prefixes gives

$$
\boxed{
R(E_0(v))=E_1(h(v)),\qquad
R(E_1(v))=E_0(AA\,h(v)).
} \tag{2}
$$

The first actual iterate is $w_1=0101=E_0(\varnothing)$. Therefore (2), by induction, codes every subsequent literal iterate. The boundary state alternates, and the token core is updated by $h$, with an $AA$ prefix added on every second step. The Lean theorem `word_coding` proves this exact correspondence.

## From the coding to the recurrence

Let

$$
\ell_j(v)=|d(h^j(v))|.
$$

Decoded length is additive under concatenation. On the three individual tokens its relevant values are

| Token | $\ell_0$ | $\ell_1$ | $\ell_3$ |
|---|---:|---:|---:|
| $A$ | 2 | 3 | 7 |
| $B$ | 3 | 4 | 10 |
| $C$ | 4 | 7 | 15 |

In every row, $\ell_3=\ell_1+2\ell_0$. Additivity gives the universal identity

$$
\ell_3(v)=\ell_1(v)+2\ell_0(v). \tag{3}
$$

The exact boundary updates (2) give the following lengths after $j$ further scans:

| Starting state | $j=0$ | $j=1$ | $j=2$ | $j=3$ |
|---|---|---|---|---|
| $E_0(v)$ | $\ell_0(v)+4$ | $\ell_1(v)+5$ | $\ell_2(v)+8$ | $\ell_3(v)+11$ |
| $E_1(v)$ | $\ell_0(v)+5$ | $\ell_1(v)+8$ | $\ell_2(v)+11$ | $\ell_3(v)+16$ |

In each row, (3) shows that the fourth entry plus 2 equals the second entry plus twice the first. Since every $w_n$ with $n\ge1$ has one of these two forms,

$$
L_{n+3}+2=L_{n+1}+2L_n\qquad(n\ge1).
$$

Subtract this identity at $n$ from the identity at $n+1$ to obtain

$$
L_{n+4}+2L_n=L_{n+3}+L_{n+2}+L_{n+1}\qquad(n\ge1).
$$

This is precisely the source recurrence, with $N=n+4$. The first five literal words have the stated lengths. Recurrence uniqueness now proves agreement with A288523 at every index. The formal reference sequence is defined independently over the integers, so no natural-number subtraction convention is hidden in the statement.

As an algebraic consequence, the length generating function is

$$
\sum_{n\ge0}L_nx^n
=\frac{2+2x-x^2-3x^3-2x^4}{1-x-x^2-x^3+2x^4},
$$

agreeing with the expression already printed in A288523. This generating-function display follows from the proved recurrence; it is not an additional formal theorem or a separately counted conjecture resolution.

## Formal verification

[Proof.lean](Proof.lean) contains the complete development under namespace `Kimberling288523`.

| Declaration | Formal conclusion |
|---|---|
| `rewrite` and `word` | Literal left-to-right, nonoverlapping binary scan and its source iterates |
| `rewrite_tail` | Exact boundary equation (1) for every finite token word |
| `rewrite_encode` | Both alternating state transitions (2) |
| `word_coding` | Every literal source iterate after the initial word has the coded form |
| `morph_length_cubic` | The additive length identity (3) for every token word |
| `length_affine` | The shorter affine recurrence with its exact starting index |
| `length_recurrence` | The source order-four recurrence for every applicable index |
| `initial_lengths` | All five literal initial lengths |
| `original_conjecture` | Equality with the independently specified integer recurrence for every natural index |

The package pins Lean **4.19.0** and mathlib revision **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. Reproduce with:

```sh
lake exe cache get
lake build
```

All printed endpoint dependencies are only `propext` and `Quot.sound`. There are no admissions, added axioms, unsafe declarations, native-evaluation proof shortcuts, or empirical recurrence assumptions. The fresh author build and independent audit are recorded in the accompanying logs and audit report.

## Sources, prior work, and scope

The assertion is Kimberling's 2017 conjecture. The exact source exports are preserved in [sources](sources), with their official Git hashes in [source_checks.md](source_checks.md).

Both search engines, the current trureturing index, related public proofs, and the latest project index were checked. No earlier proof of this exact replacement-length assertion was located. This is a bounded prior-publication check, not a certification of historical priority.

The nearby Dvořáková–Pelantová–Shallit paper concerns A288462 and the rule $00\to0101,1\to10$. The trureturing A288476 proof concerns $00\to0101,1\to011$. The earlier repository A288668 package concerns $00\to0110,10\to000$. Those are distinct rules and are explicitly credited and distinguished in the source review. Recoding a replacement system by finite tokens is a standard method; no new general method is claimed here.

The position/frequency conjectures in A288521 and A288522 and the existence of infinite limiting words are outside this package's formal scope.
