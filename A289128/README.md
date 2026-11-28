# A replacement word with nonconvergent position ratios

**Blake Stone mathematics repository · Proof developed with OpenAI Codex.**

The literal replacement word [A289128](https://oeis.org/A289128) settles three recorded assertions of Clark Kimberling:

| Source assertion | Result |
| --- | --- |
| [A289131](https://oeis.org/A289131): the proposed recurrence gives every iterate length | Proved, starting from the literal word `00`, with all six initial values and the recurrence beginning at index 6. The same assertion in A289128 is counted once. |
| [A289129](https://oeis.org/A289129): the zero-position ratio tends to $5/2$ | Refuted. The actual infinite sequence has subsequences of these ratios tending to $7/3$ and $5/2$, so the ratio has no real limit. |
| [A289130](https://oeis.org/A289130): the one-position ratio tends to $5/3$ | Refuted. Its ratios have subsequences tending to $7/4$ and $5/3$, so this ratio also has no real limit. |

The proof is formalized through the entire chain: original nonoverlapping scanner, exact finite words, nesting, the unique infinite limiting word, one-based occurrence positions, unbounded subsequence indices, and the four real limits. The nonconvergence claims concern the actual infinite position sequences.

[Formal endpoints](Proof.lean) · [Source and prior-work review](source_checks.md) · [Author build](verification.txt) · [Independent review](independent_review.md) · [Independent build](independent_build.log)

## The source definition and indexing

Let $R$ scan its input once from left to right. Replace the next matched pair using

$$00\longmapsto0010,\qquad 01\longmapsto011,\qquad 10\longmapsto010.$$

A matched pair is consumed; its newly emitted letters are not scanned again in the same pass. An unmatched letter is copied. Thus, when the remaining input begins with `11`, the first `1` is copied and scanning continues with the second `1`. A final single letter is copied. These are precisely the three rules in the source's `StringReplace` program.

Set $w_0=00$ and $w_{n+1}=R(w_n)$. The first six words are

```text
00
0010
0010010
00100100110
001001001100101010
0010010011001010100110110110
```

Their lengths are $2,4,7,11,18,28$. Iterates are numbered from zero; positions within the infinite word and occurrence ranks are numbered from one.

## An exact description by growing blocks

For $t\ge0$, put

$$A_t=0(10)^t,\qquad B_t=0(110)^t.$$

The key scanner identity, valid for every finite binary suffix $u$, is

$$R(A_tB_su)=B_tA_{2s+1}R(u). \tag{1}$$

It controls the scanner boundary, which is essential because $R$ does not preserve arbitrary concatenations. To verify it, each initial `01` of $A_t$ emits `011`, leaving a final `0`. The next block begins with `0`, so that boundary is scanned as `00` and emits `0010`. Each remaining `110` is scanned as an unmatched `1` followed by `10`, and emits `1010`. This gives (1). Also $R(A_t)=B_t$.

Define

$$t_m=2^{m+1}-1,\qquad P_0=0010,\qquad P_{m+1}=P_mA_{t_m}B_{t_m}.$$

Induction using (1) proves both

$$R(P_mu)=R(P_m)R(u),\qquad R(P_m)=P_mA_{t_m}.$$

The base word `0010` ends at a complete scanner boundary and has image `0010010`. In the induction step, (1) gives $R(A_{t_m}B_{t_m})=B_{t_m}A_{2t_m+1}$, and $t_{m+1}=2t_m+1$. Consequently the original literal iterates satisfy, for every $m\ge0$,

$$w_{2m+1}=P_m,\qquad w_{2m+2}=P_mA_{t_m}. \tag{2}$$

The next odd word appends $B_{t_m}$. Thus every iterate is a prefix of the next, including $w_0=00$. Since the lengths grow without bound, they determine a unique infinite binary word $W$.

Lean constructs this word explicitly: its zero-based letter at index $i$ is the letter at index $i$ of $P_i$. The proved bound $|P_i|\ge i+4$ makes this choice valid. Theorems `bit_stabilizes` and `infinite_word_unique` prove that it is exactly the unique limit of the literal iterates. Every later iterate with $n\ge2i+1$ has the same letter at that index.

## Exact lengths and occurrence counts

Write $L_n=|w_n|$, and let $Z_n,O_n$ be its counts of zeros and ones. Counting the blocks in (2) gives:

| Quantity | Odd iterate $n=2m+1$, $m\ge0$ | Even iterate $n=2m+2$, $m\ge0$ |
| --- | --- | --- |
| $L_n$ | $10\cdot2^m-3m-6$ | $14\cdot2^m-3m-7$ |
| $Z_n$ | $4\cdot2^m-1$ | $6\cdot2^m-1$ |
| $O_n$ | $6\cdot2^m-3m-5$ | $8\cdot2^m-3m-6$ |

The length formulas agree with the formulas Colin Barker recorded in A289131 on July 2, 2017. Those scalar formulas are credited to Barker. The result here establishes their equality with the lengths of the original replacement iterates by proving (2).

For $r\ge1$ the length formulas imply the shorter affine relation

$$L_{r+4}+2L_r=3L_{r+2}+3.$$

Subtracting two consecutive relations yields exactly the source recurrence

$$L_n=L_{n-1}+3L_{n-2}-3L_{n-3}-2L_{n-4}+2L_{n-5}\qquad(n\ge6).$$

The formal endpoint `original_length_conjecture` proves equality at every natural index with a separately defined integer recurrence having initial values $2,4,7,11,18,28$. It includes the exceptional zeroth word. No truncating natural-number subtraction is used in defining the reference recurrence.

## Actual occurrence positions and four different limiting behaviors

Let $a(k)$ and $b(k)$ be the one-based positions of the $k$-th zero and one in $W$. Both symbols occur infinitely often. In Lean these are defined using `Nat.nth` on the predicates that the zero-based letter is false or true, followed by a shift to one-based position and rank. The theorem `position_spec` proves both the letter and its exact preceding occurrence count at every positive rank.

Every positive-index iterate ends in `10`. Since each is a prefix of $W$, its final zero and final one have the exact ranks

$$a(Z_n)=L_n,\qquad b(O_n)=L_n-1\qquad(n\ge1). \tag{3}$$

This is a theorem about the infinite position maps, proved from prefix agreement and the `Nat.nth` counting identity. The four rank sequences $Z_{2m+1},Z_{2m+2},O_{2m+1},O_{2m+2}$ are strictly increasing, hence tend to infinity. Inserting the count formulas into (3) gives

$$\frac{a(Z_{2m+1})}{Z_{2m+1}}
=\frac{10\cdot2^m-3m-6}{4\cdot2^m-1}\longrightarrow\frac52,$$

$$\frac{a(Z_{2m+2})}{Z_{2m+2}}
=\frac{14\cdot2^m-3m-7}{6\cdot2^m-1}\longrightarrow\frac73,$$

$$\frac{b(O_{2m+1})}{O_{2m+1}}
=\frac{10\cdot2^m-3m-7}{6\cdot2^m-3m-5}\longrightarrow\frac53,$$

$$\frac{b(O_{2m+2})}{O_{2m+2}}
=\frac{14\cdot2^m-3m-8}{8\cdot2^m-3m-6}\longrightarrow\frac74.$$

These limits follow by dividing numerator and denominator by $2^m$ and using $m/2^m\to0$. If either full position ratio converged, both corresponding subsequences would have that same limit. The two limits differ in each case, which proves nonconvergence.

The growing blocks explain the oscillation: successive appended blocks have different symbol proportions, and their lengths remain comparable to the whole prefix. Longer samples taken at only one parity of replacement stages therefore suggest the wrong conclusion about the full position sequence.

## Formal coverage and reproducibility

| Module | Main verified content |
| --- | --- |
| `Blocks.lean` | Literal scanner; arbitrary-suffix block identity; every original iterate has the proved block form. |
| `Counts.lean` | Exact lengths, counts, positive block sizes, prefix growth, terminal `10`. |
| `Lengths.lean` | Exact source recurrence and equality with its independent integer definition. |
| `InfiniteWord.lean` | Nested iterates; unique infinite word; coordinate stabilization; one-based position maps; exact endpoint positions. |
| `Limits.lean` | Infinitely many occurrences; position specification; strictly increasing rank subsequences; all four real limits; nonconvergence. |
| `Proof.lean` | Named source refutations and axiom reports for the principal endpoints. |

Use Lean 4.19.0 and the pinned mathlib revision in the package:

```sh
lake exe cache get
lake build
sha256sum -c SHA256SUMS.txt
```

All six local modules are included in the default Lake target. The formal proofs use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; there are no admitted statements, additional axioms, or native-decision shortcuts.

The preserved primary exports and bounded prior-publication search are documented in [source_checks.md](source_checks.md). No earlier proof or refutation of these exact assertions was located. This is not a claim of exhaustive historical priority or OEIS editorial acceptance. This package claims exactly one shared length conjecture and two position-limit refutations; it does not count the repeated length comment in A289128 as an additional result, and it does not provide a corrected classification of the accompanying all-index inequalities in A289129/A289130.
