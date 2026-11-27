# Three questions on Jeffery's matrix array

Row $n$ of A205573 counts walks with maximum height at most $n$. An unrestricted walk on the integer line folds into a dispersed Dyck path, giving the entry $\binom{j}{\lfloor j/2\rfloor}$ through column $2n+1$. At column $2n+2$ exactly one path is lost. Independent mathematical review is pending. [Manuscript (PDF)](bounded-walks.pdf) · [LaTeX](bounded-walks.tex) · [A205573](https://oeis.org/A205573)

The column generating function sums Emeric Deutsch's exact-height counts. The reduced row denominator has degree $n+1$, correcting the printed upper limit in Jeffery's second conjecture and agreeing with his worked example. The paper gives the exact row indexing in both coefficient triangles. [A191314](https://oeis.org/A191314) · [A108299](https://oeis.org/A108299) · [A115139](https://oeis.org/A115139)

Run `python3 verify.py` to compare 13 matrix sizes, the generating functions, and all walks through length 14. [Verifier](verify.py)
