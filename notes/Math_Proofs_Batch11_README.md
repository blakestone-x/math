# Batch 11: a complete irreducibility classification and three recurrence refutations

**Blake Stone · Proof developed with ChatGPT · November 27, 2026**

[Read the complete manuscript](Math_Proofs_Batch11.pdf) · [LaTeX source](Math_Proofs_Batch11.tex) · [Mathematical and formal review](Math_Proofs_Batch11_math_review.md) · [Rendering record](Math_Proofs_Batch11_review.md)

This batch addresses **four recorded source assertions in two proof projects**: one full irreducibility classification and three related length-conjecture refutations. The three word systems have the same exact length dynamics, so their refutations follow from one common theorem. The repeated assertion in A289001 and A289004 is counted once. Supporting lemmas, corrected source typos, and strengthened conclusions do not inflate the count.

| Project | Exact result | Source assertions |
|---|---|---:|
| [A327315](../A327315/README.md) | The normalized derivative numerator is irreducible exactly when its degree is $2^a3^b$. The theorem includes every derivative order and the exact canonical numerator. | 1 classification |
| [A289004](../A289004/README.md) | The literal iterates in A289001, A289035, and A289239 first disagree with their proposed common length sequence at iteration 22. Their true growth ratio is $1+\sqrt2/2$, and no eventual monic integer linear recurrence can describe their lengths. | 3 related refutations |

## 1. Complete classification for the derivative polynomials

Let $P_n$ be the reduced numerator of

$$
\frac{d^n}{dX^n}\left(\frac{X-2}{X^2-X+1}\right),
$$

divided by $n!$, with the denominator monic. Then, for every $n\ge0$,

$$
\boxed{P_n\text{ is irreducible over }\mathbb Q
\iff n+1=2^a3^b\text{ for some }a,b\ge0.}
$$

The source's actual row degree is $n+1$, as shown by its program and displayed rows. Its initial row is $P_0=X-2$.

The proof defines degree-indexed polynomials

$$
S_0=-1,\qquad S_1=X-2,\qquad
S_{N+2}=(1-2X)S_{N+1}-(1-X+X^2)S_N.
$$

Differential identities and coprimality establish the exact formula

$$
\left(\frac{X-2}{1-X+X^2}\right)^{(n)}
=\frac{n!S_{n+1}}{(1-X+X^2)^{n+1}},
\qquad P_n=S_{n+1}.
$$

Over $K=\mathbb Q(u)$, where $u^2-u+1=0$ and $v=1-u$, the row is a nonzero scalar times

$$
(X-u)^N-v(X-v)^N.
$$

When $N=2^a3^b$, the identity

$$
Y^{2N}-Y^N+1=\Phi_{6N}(Y)
$$

and the quadratic tower degree show that $Y^N-v$ is irreducible over $K$. A fractional-linear substitution gives irreducibility of $S_N$ over $K$, hence over $\mathbb Q$.

For every other positive $N$, choose a prime $p>3$ dividing it and write $N=pm$. If $p\equiv1\pmod6$, then $S_m$ divides $S_N$. If $p\equiv5\pmod6$, then $S_m(1-X)$ divides $S_N$. These divisibilities descend to $\mathbb Q[X]$ and give explicit nonconstant proper factors.

The family has an exact connection with Remete's generalized simplest polynomials, which is credited in the package. Cyclotomic irreducibility and fractional-linear substitution are classical ingredients. The contribution is the complete stated degree criterion and its formal connection with the literal source numerator.

## 2. Three length conjectures refuted, with a stronger structural result

Each system begins with $w_0=00$, uses the common rules

$$
00\mapsto0010,\qquad 10\mapsto010,
$$

and chooses its middle rule as follows:

| Source | Rule for $01$ |
|---|---|
| A289001, also cited in A289004 | $01\mapsto001$ |
| A289035 | $01\mapsto010$ |
| A289239 | $01\mapsto100$ |

The scan consumes nonoverlapping matched pairs and retains a final singleton, as the source programs do. If $L_n$ and $O_n$ are the length and one-count, all three systems satisfy

$$
L_0=2,\quad O_0=0,\qquad
O_{n+1}=\left\lfloor\frac{L_n}{2}\right\rfloor,\qquad
L_{n+1}=2L_n-O_n-(L_n\bmod2).
$$

The proof derives these equations from the literal scanner and an invariant excluding adjacent ones and a terminal one. It does not assume the proposed linear recurrence.

The proposed length sequence is A289004, independently defined by an order-ten integer recurrence. The first mismatch is certified exactly:

$$
L_n=\operatorname{A289004}(n)\quad(0\le n<22),\qquad
L_{22}=268184\ne268182=\operatorname{A289004}(22).
$$

For all $n$ we also prove

$$
0\le L_n-(2+\sqrt2)O_n\le2,
\qquad
\lim_{n\to\infty}\frac{L_{n+1}}{L_n}=1+\frac{\sqrt2}{2}.
$$

This gives a general obstruction. If an eventual constant-coefficient recurrence with integer coefficients existed, its monic characteristic polynomial would vanish at $\lambda=1+\sqrt2/2$. That would make $\lambda$ an algebraic integer, hence make $(\lambda-1)^2=1/2$ an algebraic integer, which is impossible.

The formal endpoint states that **every monic integer polynomial relation fails beyond every finite cutoff**. The claim is about ordinary recurrences with leading coefficient one and integer coefficients; it is not a claim about arbitrary real-coefficient relations. The source's order-ten recurrence cannot be repaired by changing finitely many initial values.

Earlier fixed-point and final-letter-removed results are credited and kept distinct from these literal retained-singleton iterate lengths.

## Verification and reproducibility

Both projects pin Lean **4.19.0** and mathlib commit **`c44e0c8ee63ca166450922a373c7409c5d26b00b`**. Each is a standalone Lake project:

```sh
lake exe cache get
lake build
```

The algebra package contains nine proof modules; the replacement package contains seven. All local proof modules are explicit Lake roots. Author and independent builds use fresh project directories, copy only source/configuration files, and reuse only the pinned external dependency cache. They do not reuse local proof objects. Each package includes its build transcripts, source hashes, source snapshots, bounded prior-publication review, and mathematical audit.

The theorem endpoints depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The proof sources contain no admissions, custom axioms, unsafe declarations, or native-evaluation shortcuts.

## Attribution correction accompanying this release

The release also corrects Batch 10's treatment of A211417. A September 19, 2026 report in VladimirReshetnikov/ProveIt already proved the entire positive-shift integrality family and a stronger classification. Our verified Lean source is retained unchanged and is now labeled an **independent formalization of prior work**. It is not counted as a new result in Batch 11.

The [corrected Batch 10 guide](Math_Proofs_Batch10_README.md), [dated correction record](Math_Proofs_Batch10_correction_2026-11-27.md), and [exact prior-proof report](../A211417/PRIOR_PROOF.md) identify the predecessor and preserve the original audit history. The narrower initial searches missed it; broader semantic GitHub searches are now included in screening.

For the current Batch 11 claims, no earlier exact resolution was found in the checked primary references and bounded public searches. That statement is a search result, not a guarantee of worldwide historical priority or a claim of OEIS editorial acceptance.
