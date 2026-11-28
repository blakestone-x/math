# A288668: an exact word identity for Kimberling's binary replacement

**Blake Stone** · Proof developed with OpenAI Astra 6.2 · November 27, 2026

## Result

Start with the binary word $w_0=00$. To obtain the next word, scan from
left to right, replacing nonoverlapping occurrences according to

$$
00\longmapsto0110,\qquad 10\longmapsto000.
$$

Copy any letter that does not begin a matching pair. This is the literal
`StringReplace` operation in [OEIS A288665](https://oeis.org/A288665).
We prove the stronger word identity

$$
\boxed{w_{n+3}=w_n\,w_n\,w_{n+1}\qquad(n\ge0),}
$$

where juxtaposition denotes concatenation. In particular, the lengths

$$
L_n=|w_n|=2,4,5,8,13,18,29,44,65,102,\ldots
$$

obey

$$
\boxed{L_{n+3}=L_{n+1}+2L_n,\qquad L_0=2,\ L_1=4,\ L_2=5.}
$$

This proves the conjectured connection between the replacement process
and [A288668](https://oeis.org/A288668), recorded by Clark Kimberling in
2017. The same assertion appears in both A288665 and A288668; it is
**one resolved assertion**, counted once.

The formal proof begins with literal lists of bits and the actual
replacement operation. It proves the coding bridge and the word identity,
then derives the recurrence for every iterate. It does not infer the
recurrence from a finite table.

### Source indexing

The A288668 data, generating function, and Mathematica program consistently
specify the three initial values $2,4,5$ at indices $0,1,2$.
Its title and repeated formula instead label them $0,2,3$, an indexing
error. The proved connection uses the coherent sequence defined by its
data and executable program, and explicitly records the corrected labels.
The source notes below describe two additional cross-reference errors;
none is counted as another conjecture resolution.

## Three tokens give a proof for every iterate

Introduce three letters with binary codes

$$
A=00,\qquad B=0110,\qquad C=01000.
$$

One replacement pass gives

$$
A\longmapsto B,\qquad B\longmapsto C,\qquad C\longmapsto AAB.
$$

These identities remain valid when an arbitrary suffix follows the token.
Each token finishes with a pair that is consumed by the scan: $00$ for
A and C, and $10$ for B. No matching pair crosses that token boundary.
For example,

$$
0110\longmapsto0\,1\,000=01000,
\qquad
01000\longmapsto0\,000\,0110=00\,00\,0110.
$$

Consequently, if $\phi$ is the substitution

$$
\phi(A)=B,\quad \phi(B)=C,\quad \phi(C)=AAB,
$$

extended to concatenations, then decoding $\phi^n(A)$ gives exactly
the literal binary word $w_n$. This equality is proved in Lean as
`word_eq_decode`, using the stronger arbitrary-suffix lemma
`rewrite_decode_append`.

Now $\phi^3(A)=AAB$. Applying $\phi^n$ and decoding gives

$$
w_{n+3}=w_nw_nw_{n+1}.
$$

The first three actual words are $00$, $0110$, and $01000$, of lengths
$2,4,5$. Taking lengths proves the stated recurrence and its initial
conditions. Strong induction identifies all its terms with the reference
sequence A288668.

## Additive weights and the three limiting words

The word identity works for every assignment of nonnegative integer
weights to the bits. If each zero receives weight u and each one weight v,
and $W_n$ is the total weight of $w_n$, then

$$
W_{n+3}=W_{n+1}+2W_n,
$$

with

$$
W_0=2u,\qquad W_1=2u+2v,\qquad W_2=4u+v.
$$

Thus the length, zero count, and one count have the same recurrence.
The first three cases and their ordinary generating functions are:

| Statistic | Initial values | Generating function |
|---|---|---|
| Length | 2, 4, 5 | $(2+4x+3x^2)/(1-x^2-2x^3)$ |
| Number of zeros | 2, 2, 4 | $(2+2x+2x^2)/(1-x^2-2x^3)$ |
| Number of ones | 0, 2, 1 | $(2x+x^2)/(1-x^2-2x^3)$ |

The generating functions follow by multiplying the respective recurrence
by powers of x and collecting coefficients. The length formula agrees
with the one already given in A288668. The universal weighted recurrence
is a formal theorem; the generating-function displays are its elementary
algebraic consequences.

The concatenation identity also shows that $w_n$ is a prefix of
$w_{n+3}$. More generally, for every $n,t\ge0$, Lean proves

$$
w_n\text{ is a prefix of }w_{n+3t},\qquad
|w_{n+3t}|\ge2^t|w_n|.
$$

The lengths are positive and increase strictly along each phase.
Therefore each residue class modulo three consists of nested words
whose lengths tend to infinity, establishing the three infinite limits
used in A288665, A288670, and A288673. These consequences of the same word
identity are not counted as additional conjecture resolutions.

## What the formal proof establishes

[Proof.lean](Proof.lean) contains the complete development.

| Declaration | Meaning |
|---|---|
| `rewrite` | The literal left-to-right scan of binary lists. |
| `word_eq_decode` | Every source iterate is exactly the decoded token iterate. |
| `word_three_steps` | The exact concatenation identity for every n. |
| `weighted_recurrence` | The recurrence for every additive nonnegative bit weight. |
| `length_recurrence` and `initial_lengths` | The conjectured length recurrence and correct bases. |
| `original_conjecture` | Equality with the A288668 reference sequence for every n. |
| `phase_prefix` and `phase_length_growth` | Nested prefixes and exponential growth in every phase. |

The recurrence reference uses the data/program's initial indices $0,1,2$,
with the source ambiguity documented in its definition. No part of the
literal word process is replaced by an assumed counting recurrence.

## Sources and prior work

The complete official OEIS snapshots are preserved in [sources](sources).
The two relevant entries retain the length assertion as a conjecture.
Both search engines, the live trureturing index, and semantic searches for
the replacement rules did not locate an earlier proof of this particular
connection. This is a bounded search record, not a certification of
historical priority or OEIS editorial acceptance.

The earlier repository package [Kimberling pair rules](../Kimberling-pair-rules/README.md)
handles different replacements: $00\to001$, with either $1\to000$ or
$1\to010$. Its results are not repeated here. Finite coding and substitution
methods are standard; the contribution here is the exact three-token
description and complete checked proof for this specific replacement.

[source_checks.md](source_checks.md) records the entry versions, prior-proof
searches, and clerical source issues. In particular, A288670 and A288673
refer to A288468 for the lengths; the intended reference is A288668.
A288468 is a different position sequence with a different defining
replacement. These incorrect links are documented, not counted as
independent mathematical refutations.

## Reproduce

The package pins Lean 4.19.0 and mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run:

```sh
lake exe cache get
lake build
```

The public theorem axiom reports contain only the standard Lean axioms,
as applicable. There are no unfinished proofs, custom axiom declarations,
external proof oracles, or `native_decide` calls.

[verification.txt](verification.txt) records the fresh standalone build.
The separate [AUDIT.md](AUDIT.md) and [audit-verification.txt](audit-verification.txt)
record the independent review and compilation. `SHA256SUMS.txt` identifies
the delivered files.
