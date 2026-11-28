# Runs with prescribed fractional digits in a square root

Fix a base, a word of digits of width $j$, its value $h$, and $W=b^j$. For integer part $k$ the complete block of radicands runs from $L_h(k)$ through $L_{h+1}(k)-1$, where $L_h(k)=\lceil(Wk+h)^2/W^2\rceil$. Block length increases by exactly two when $k$ increases by $W$. All sufficiently late blocks are nonempty. Their start sequence has a rational generating function with denominator dividing $(1-z)^2(1-z^W)$. [Manuscript](blocks.pdf) · [LaTeX](blocks.tex)

| Specialization | Result |
|---|---|
| All ten decimal leading digits | The finite initial rows and an explicit formula for every run start of A034106 through A034115, with squares excluded for digit zero. |
| A034097 | Papadopoulos's proposed rounded length is exact for every integer part, including empty blocks. |
| A034108 | Both of Chai Wah Wu's conjectured formulas follow, including the recurrence starting at index 9 and the numerator of the generating function. |
| A063656 | The square-started blocks occupy triangular indices. This proves Lowell's greedy rule, starting with the source's offset zero. |

Run `python3 verify.py` to compare 30,456 blocks against direct scaled integer square roots across twelve values of $W$, reproduce all ten decimal start tables, and check the recurrence and triangular indexing. Lean checks the exact membership inequalities and the rounded length for every integer part. [Verifier](verify.py) · [Expected output](checks.txt) · [Lean lemmas](Prefix.lean)

Earlier contributions to Left to Solve also address the three individual conjectures. [A034097](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2504) · [A034108](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/13440) · [A063656](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/14929)
