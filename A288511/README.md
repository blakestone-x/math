# A288511: an exact proof of the thirteen-term replacement-length recurrence

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

Starting with the binary word $w_0=00$, scan left to right and make the nonoverlapping replacements

$$00\longmapsto0101,\qquad 10\longmapsto001.$$

An unmatched letter is copied and the scan advances by one position. Write $L_n=|w_n|$. We prove the length conjecture in [OEIS A288511](https://oeis.org/A288511), repeated in [A288508](https://oeis.org/A288508) and [A288512](https://oeis.org/A288512): **the literal length is the specified recurrence sequence at every natural index, including zero**. The three entries state the same length assertion and are counted as one resolution.

Explicitly, for $n\ge16$,

$$
\begin{aligned}
L_n={}&2L_{n-1}-L_{n-2}+2L_{n-3}-4L_{n-4}+4L_{n-5}-4L_{n-6}\\
&+4L_{n-7}-4L_{n-8}+4L_{n-9}-3L_{n-10}+2L_{n-11}-3L_{n-12}+2L_{n-13},
\end{aligned}
$$

with the source's initial values

$$
(L_0,\ldots,L_{15})=(2,4,5,7,9,12,17,23,33,48,70,103,152,228,343,515).
$$

The proof identifies the finite words themselves with a three-letter substitution and a ten-state boundary cycle. The recurrence is then an identity in four unrestricted integer coordinates, followed by recurrence uniqueness. No asymptotic density, infinite-word identification, or guessed recurrence is assumed.

## 1. Interior coding and the literal scanner

Use the binary codes

$$h(A)=10,\qquad h(B)=100,\qquad h(C)=1000,$$

and extend $h$ to finite words by concatenation. Define

$$\sigma(A)=B,\qquad \sigma(B)=C,\qquad \sigma(C)=AAB.$$

Let $T$ be one literal scan. When a code block is followed by a word starting in $1$, its scan is independent of that following word. The three emitted blocks are

$$r(A)=001,\qquad r(B)=0010,\qquad r(C)=0010101.$$

In each case

$$r(X)00=00h(\sigma(X)).$$

For example, $r(C)00=001010100=00h(AAB)$. Induction on a finite token word $v$ therefore gives

$$r(v)00=00h(\sigma(v)). \tag{1}$$

This controls the scanner boundary. It does not assert that $T$ preserves arbitrary binary concatenations: that would already fail on the concatenation of two singleton zeros. The formal statements `rewrite_block`, `rewrite_encode`, and `rotation` establish the needed identities directly from the recursive source scan.

## 2. The ten boundary states

For a phase $i\in\{0,\ldots,9\}$, a token word $v$, and $t\ge0$, define

$$F_i(v,t)=0^{b_i}h(v)h(s_i)1^{t+1}.$$

All phase subscripts are taken modulo ten. The following table gives every parameter in the update.

| $i$ | $b_i$ | $s_i$ | $\ell_i$ | $e_i$ | $d_i$ |
|---:|---:|:---|:---|:---|---:|
| 0 | 1 | BAA | empty | empty | 1 |
| 1 | 3 | CB | AC | A | 0 |
| 2 | 1 | ABA | empty | empty | 1 |
| 3 | 3 | BC | AC | empty | 1 |
| 4 | 1 | CAA | empty | A | 1 |
| 5 | 3 | ABB | AC | empty | 0 |
| 6 | 1 | BCA | empty | C | 1 |
| 7 | 3 | AAB | AC | empty | 0 |
| 8 | 1 | BBA | empty | empty | 1 |
| 9 | 3 | CC | AC | AA | 1 |

The exact scanner equation is

$$\boxed{T(F_i(v,t))=F_{i+1}(\ell_i\sigma(v)e_i,\ t+d_i).} \tag{2}$$

Here is how to verify the table. Scanning the suffix $h(s_i)1^{t+1}$ gives $00h(e_i)h(s_{i+1})1^{t+1+d_i}$. For instance, the first two suffix transitions are

$$\begin{aligned}
T(h(BAA)1^{t+1})&=00h(CB)1^{t+2},\\
T(h(CB)1^{t+1})&=00h(A)h(ABA)1^{t+1}.
\end{aligned}$$

Equation (1) moves this initial $00$ through the coded core. If $b_i=1$, the leading unmatched zero produces the next prefix $000$. If $b_i=3$, the scan of the initial three zeros, followed by the $00$ from the interior, is $0101000=0h(AC)$. This accounts for $\ell_i$. All remaining suffix cases are the finite scanner equalities in the table. In Lean, `rewrite_suffix` checks them with an arbitrary natural $t$, and `rewrite_shape` then proves (2) for every finite token word $v$.

The ninth literal iterate has the exact representation

$$w_9=F_0(ACCBBCBBCAA,5). \tag{3}$$

Consequently, (2) and (3) describe every $w_n$ for $n\ge9$. The token core contains $3$ letters $A$, $4$ letters $B$, and $4$ letters $C$ at this starting point. The formal theorem `word_shape` proves the full binary-word equality at every subsequent index.

## 3. Why an order-thirteen recurrence appears

Let $(a,b,c)$ be the numbers of $A,B,C$ in the core. The substitution changes these to

$$M(a,b,c)=(2c,a+c,b),\qquad M^3=M+2I.$$

The phase update adds the counts of $\ell_i e_i$, while $t$ increases by $d_i$. The word length in this state is

$$\mathcal L(i,a,b,c,t)=2a+3b+4c+t+1+b_i+|h(s_i)|. \tag{4}$$

Equations (2) and (4) give a four-coordinate affine state update with a ten-periodic phase. This provides an efficient exact description even when the literal word is enormous.

The following calculation explains the factorization of the recurrence. Let $E$ mean a shift by one iterate, and put

$$R_n=L_{n+3}-L_{n+1}-2L_n.$$

The identity $M^3=M+2I$ cancels all three core counts. At phase $i$ and current trailing coordinate $t$, the remaining value is $R=-2t+q_i$, with

$$
(q_0,\ldots,q_9)=(-4,-3,-3,-3,-4,-3,-4,-3,-3,-3).
$$

Now set

$$S_n=R_n+R_{n+2}+R_{n+4}+R_{n+6}+R_{n+8}.$$

Using the same ten-state table gives $S=-10t+u_i$, where

$$
(u_0,\ldots,u_9)=(-44,-41,-48,-45,-42,-39,-46,-43,-50,-47).
$$

Every row satisfies $-10d_i+u_{i+1}-u_i=-7$. Hence $S_{n+1}-S_n=-7$, and therefore

$$
\boxed{(E-1)^2(1+E^2+E^4+E^6+E^8)(E^3-E-2)L=0.} \tag{5}
$$

Expanding the monic polynomial in (5) gives exactly the order-thirteen recurrence printed in A288511. The argument initially applies when the smallest index in the recurrence is at least nine, so the newest index is at least twenty-two. The remaining six instances at newest indices $16,\ldots,21$ follow from the explicitly evaluated literal lengths. Together with the sixteen initial values, this proves the source conjecture for every index by strong induction.

The Lean proof establishes (5)'s expanded recurrence directly as a universal identity for every phase and four arbitrary integer coordinates. Its short, explicit intermediate states are proved by normalization, ring identities, and kernel computation. The separate natural-number induction then transports that identity to the literal words. The displayed $R,S$ calculation is an explanatory derivation of the same polynomial; it is not an extra assumption used by the formal proof.

## 4. Generating-function indexing correction

As an algebraic consequence of the proved recurrence and initial values,

$$\sum_{n\ge0}L_nx^n=\frac{N(x)}{D(x)},$$

where

$$D(x)=(1-x)^2(1-x^2-2x^3)(1-x+x^2-x^3+x^4)(1+x+x^2+x^3+x^4)$$

and

$$N(x)=2-x^2-3x^3-x^5-x^7-x^9-x^{10}-3x^{11}+x^{12}+2x^{13}+x^{14}-2x^{15}.$$

The source displays $xN(x)/D(x)$. With the source's offset zero, that extra $x$ shifts the series by one: its constant coefficient is $0$, whereas $L_0=2$. Our target is the independently recurrence-defined sequence and its literal length assertion. The correctly indexed generating function above is a corollary of that result, not a separately counted conjecture resolution or an additional Lean power-series theorem.

## Formal proof scope and reproduction

The final theorem is

```lean
Kimberling288511.all_lengths (n : ℕ) :
  ((Kimberling288511.word n).length : ℤ) = Kimberling288511.source n
```

| File | Role |
|---|---|
| `Blocks.lean` | Literal scan, exact block conjugacy, all ten boundary transitions |
| `Counts.lean` | Equality of literal finite words with the state model; length bridge |
| `Recurrence.lean` | Universal recurrence certificate, initial values, independent reference sequence, all-index equality |
| `Proof.lean` | Public endpoint and explicit axiom audit |

Build with `lake build` using the included Lean 4.19.0 toolchain and pinned mathlib commit. Every local proof module is an explicit Lake root. The proof uses no `sorry`, `admit`, custom axiom, or `native_decide`. Ordinary `decide` is used only for finite, kernel-reducible data and checks; the arbitrary-word and arbitrary-index arguments are symbolic inductions.

`verify.py` supplies supplementary checks with two independently coded literal scanners, the complete boundary table for 3,630 selected inputs, a state/recurrence comparison through index 2,000, and all affine-certificate basis coefficients. These computations are not the evidence for the unbounded theorem; the Lean proof supplies that evidence.

## Prior work and novelty boundary

The exact current OEIS source exports are archived in `sources/`. The source still explicitly labels the length assertion as a conjecture. Exact-ID, literal-rule, and semantic searches were also conducted in both web search engines, global GitHub code, `VladimirReshetnikov/ProveIt`, and the current trureturing collection. They located source mirrors, recurrence implementations, and proofs of different Kimberling rules; no matching proof of this literal assertion was found in that bounded screen.

Finite recoding of context-dependent word operations is a standard method. Related work includes Dvořáková, Pelantová, and Shallit's [Tribonacci analysis](https://dmtcs.episciences.org/articles/17782), concerning A288462/A288465, and trureturing's [A288476 length proof](https://www.trureturing.org/research/oeis-a288476-replacement-iterate-length/), concerning $00\to0101,1\to011$. Neither is the present $00\to0101,10\to001$ assertion. This package claims the exact source result, not a new general recoding method or a worldwide priority guarantee. Details and search locators appear in `source_checks.md`.
