# The exact power of two in cubic Franel sums

For every $q\ge4$, exactly $3q-2$ powers of two divide the cubic Franel number $f_{2^q-1}$, where $f_n=\sum_{k=0}^n\binom nk^3$. Thus the first fixed exponent in Fabius Wiesner's question holds on every proposed row, including $q=4$. The actual valuations at $q=1,2,3$ are $1,3,9$. The previous paper checked $4\le q\le22$ and refuted the original cutoff when all exponents vary. [Original question](https://mathoverflow.net/q/496222) · [Previous paper](../Franel-prime-power-rows/README.md) · [New manuscript](cubes.pdf) · [Editable LaTeX](cubes.tex)

| Scope | Result |
|---|---|
| $n=u2^q-1$, $u$ odd and positive, $q\ge4$ | Put $c=2q+1+3s_2(u-1)-s_2(3u-1)$, where $s_2$ counts binary ones. If $2^q-2\ge c+q-1$, then $v_2(f_n)=c+q-2$. This covers every fixed $u$ for all sufficiently large $q$. |
| Examples | $u=1$ gives $3q-2$ and $u=3$ gives $3q+1$, both for every $q\ge4$. |
| Normalized values | With $C_n=(3n)!/(n!)^3$, the units $4f_n/((n+1)C_n)$ converge to the same value for every fixed odd $u$. Its residue modulo $4096$ is $1959$. The paper gives an explicit error bound at every Taylor order. |
| Next exponent | Whether $v_2(\sum_k\binom{2^q-1}k^5)=3q-1$ for all sufficiently large $q$ remains open here. |

The proof rewrites the cube sum as a factorial sum. At the limiting row $n=-1$, the whole associated series adds to zero in the 2-adic numbers by a double-angle identity. In the difference between the row sum and this limiting series, one term has strictly smaller valuation than every other term.

## Verification

The Python verifier checks every qualifying row through $n=12{,}000$ by the integer Franel recurrence, with direct binomial sums through $n=120$. A second method uses the factorial sum modulo a power of two and tests five multipliers at exponents through $q=1000$. A harmonic-series check independently recovers the first twelve bits of the limiting unit. Run `python3 -B verify.py`. [Verifier](verify.py) · [Expected output](verification.txt)

Lean 4.33.1 checks the valuation of the decisive first difference. A separate complete Lean disproof of the source’s uniform conjunction uses $(q,m)=(5,19)$ and passed Left to Solve’s pinned proof and axiom checker locally. The manuscript supplies the infinite-series argument for exponent three. The site reviews a first statement before opening its proof step. [First-difference lemma](FirstTerm.lean) · [Checked disproof](proofs/mo-496222.lean) · [Proposed target](OMAStatements/S_mo_496222.lean) · [Statement review #22393](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22393)

To reproduce the formal results, use Lean 4.33.1 and the Mathlib dependencies of formal-conjectures at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. Compile the proposed target under module name `OMAStatements.S_mo_496222` before the disproof. Its statement has the review placeholder required by the site. The disproof only uses the type of the target.
