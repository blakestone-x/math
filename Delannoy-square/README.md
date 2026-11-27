# Simple negative zeros of squared Delannoy rows

**Every degree-$n$ row polynomial of the ordinary matrix square of the Delannoy triangle has $n$ distinct negative zeros.** This proves the Delannoy clause of Mao and Wang’s Conjecture 4.1. Their other clause asks the same real-rootedness question about the Eulerian triangle. [Original conjecture, Section 4](https://arxiv.org/abs/2607.01572v1) · [Proof manuscript (PDF)](manuscript.pdf) · [Editable LaTeX](manuscript.tex)

| Result | Scope |
|---|---|
| Weighted products | If a northeast step has weight $a$ in the first triangle and $b$ in the second, all zeros of every positive-degree row of $D_aD_b$ are simple and negative for $a>0$ and $b\ge 1/3$. This threshold in $b$ is exact for a guarantee covering every $a>0$. As an example below it, the third row at $a=1/16$, $b=1/5$ already has a nonreal conjugate pair. East and north steps have weight one. |
| Sharp interval | For the unweighted square, all zeros lie strictly between $-4-3\sqrt{2}$ and $-3+2\sqrt{2}$. As the row index tends to infinity, the two extreme zeros tend to these respective endpoints. |
| Largest input interval | The transformation $T_b(x^k)=d_k^b(x)$ preserves real-rootedness for every polynomial with all zeros in $[-R,0]$ exactly when $R\le b+\sqrt{b(b+1)}$. Each input $(x+c)^n$ with $c>b+\sqrt{b(b+1)}$ produces a number of nonreal zeros growing at least linearly with $n$. |
| Finite checks | The verifier constructs the triangles in two ways, performs ordinary matrix multiplication, checks the authors’ fourth-order recurrence, and isolates the stated number of simple negative zeros using exact rational signs. |

The argument follows the characteristic roots of each ordinary row. A divided difference supplies a sequence of alternating signs from arguments along a semicircle. On the real portion of the parametrization, explicit Chebyshev samples continue the alternation through the remaining degrees. An earlier proof-development project established the partial semicircle count and proposed the complementary sampling approach. Wang, Zheng and Chen studied the zeros of the single Delannoy triangle. [Earlier partial result](https://the-omega-institute.github.io/trureturing-mdbook/Problems/mao-wang-2026-delannoy-square-negative-roots.html) · [Single-triangle result](https://doi.org/10.1016/j.disc.2019.04.003)

Run `python3 -B verify.py` with the Python standard library. It checks unweighted rows 1 through 48 and four pairs of rational weights through row 22. The analytic proof covers arbitrary degrees and the full range of weights above. [Verifier](verify.py)
