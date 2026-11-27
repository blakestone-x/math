# Exact periods in the XOR Pascal triangle

In Franklin T. Adams-Watters’s triangle with diagonal entry $n$, column $k$ has least period equal to the smallest power of two at least $k$. At bit $j$, the corresponding threshold is $k-2^j+1$, or the bit vanishes if $2^j>k$. The period begins at the diagonal.

We obtain a binomial formula for every bit. In row $2^J$, the power-of-two columns contain their own index and all other entries vanish. Reflecting the triangle yields the proposed translated copies. [A195916](https://oeis.org/A195916) · [A195915](https://oeis.org/A195915)

[Manuscript](xor-triangle.pdf) · [LaTeX source](xor-triangle.tex) · [Lean proof](Periods.lean) · [Exact verifier](verify.py)

Run `lean Periods.lean` with Lean 4.19.0 to verify the exact column and bit periods, reflected copies, and dyadic rows at every index. Run `python3 verify.py` to build both array orientations and check the binomial formula directly.
