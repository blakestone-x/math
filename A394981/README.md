# A394981 · Tilings by one bar of every length

Blake Stone · Proof developed with OpenAI Codex.

Gary Yane proposed that, for odd $n$, adding the next bar multiplies the number of minimum-perimeter rectangle tilings by four. This holds for every odd $n\ge3$. The only exception is $a(1)=a(2)=1$.

Each odd-board tiling extends to an even-board tiling in exactly four ways when the height is at least two. The bar whose length equals the height either fills the left or right boundary column, or pairs horizontally with the next longer bar in a single row in either order. Each construction recovers a unique odd-board tiling. The manuscript also gives a recurrence counting every term and its factorial asymptotic.

[Illustrated manuscript](tilings.pdf) · [LaTeX source](tilings.tex) · [Verification script](verify.py) · [OEIS A394981](https://oeis.org/A394981)

The script compares all 20 terms in OEIS revision 42 against the recurrence. Run `python3 verify.py --through 12` to check the fixed-board counts independently by placing every bar directly for each of the first twelve boards.
