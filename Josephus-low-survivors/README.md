# Low Josephus survivors

Blake Stone · Proof developed with OpenAI Codex

Fix the step size $k\ge2$. Which population sizes $n\ge k$ leave a survivor with one of the first $k-1$ labels? Petros Hadjicostas proposed taking $T_1=1$ and rounding the sum of all previous terms divided by $k-1$ upward to obtain each next term. We prove that this lists every qualifying population exactly once after the initial small values. [Original conjecture, A005427](https://oeis.org/A005427) · [Step-five example, A120160](https://oeis.org/A120160) · [Manuscript (PDF)](low-survivors.pdf)

If $D_i=T_1+\cdots+T_{i+1}$ and $n=T_{i+2}\ge k$, the survivor label is $1+(k-1)n-D_i$. The proof identifies the partial sums with the classical ceiling orbit of Graham, Knuth and Patashnik. It gives the proposed label update and an exact membership test for every survivor label. The Lean development starts at the ordinary modular Josephus recurrence. [Complete discrete proof](Josephus.lean) · [Classical iteration in Odlyzko and Wilf](https://doi.org/10.1017/S0017089500008272) · [LaTeX source](low-survivors.tex)

## Distribution over population sizes

Let $A_x(N)$ count the $n\le N$ for which $J_k(n)/n\le x$, where $0<x<1$. Its lower and upper asymptotic proportions are $(k-1)x/(k-x)$ and $x$. Every intermediate proportion is a subsequential limit. The logarithmic density is $\log(k/(k-x))/\log(k/(k-1))$. These analytic assertions have written proofs in Section 4.

## Verification

```sh
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

The audit compares 6.3 million step/population pairs, simulates 4,725 circles directly, and checks the extremal frequency formulas at 33 step/threshold combinations. [Verification record](verification.txt) · [Audit code](verify.py)
