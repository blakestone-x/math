# Exact valuations on binomial rows one below a prime power

Let $F_n(r)=\sum_{k=0}^n\binom nk^r$. Fabius Wiesner asked for the valuations of these power sums on rows $p^q-1$. The odd-prime formula holds for every exponent and row in the question. The proposed fixed binary cutoff fails already at $q=5$, $m=19$. [Original question](https://mathoverflow.net/q/496222) · [Proof manuscript](manuscript.pdf) · [LaTeX](manuscript.tex)

| Scope | Result |
|---|---|
| Every odd prime $p$, $q\ge1$, even $r\ge2$ | $v_p(F_{p^q-1}(r))=q+v_p(r-1)$. In particular $r=p^m+1$ gives the proposed $q+m$. A signed difference formula gives an isometric bijection of the $p$-adic integers in the exponent variable. |
| Every fixed binary row $n=2^q-1$ | $v_2(F_n(2^m+1))=n$ for $m\ge\max(1,n-2)$. Any cutoff in $q$ must depend on $m$. Whether there is such a cutoff for every fixed $m$ remains open. |
| Every $4\le q\le22$, all $m\ge1$ | Put $h=3q-3$. The valuation equals $\min(n,m+h)$ when $n\ne m+h$, and $n+2$ at equality. At $q=5,m=19$ the valuation is 33, exceeding the proposed 31. |

The odd-prime theorem follows from summation by parts and an elementary binomial congruence. For the binary row classification, a uniform lifting lemma reduces infinitely many exponents to at most 62 per row. The C++ program calculates the finite residues modulo $2^{128}$. A separate Python verifier uses literal binomial coefficients at smaller sizes. [C++17 certificate](binary_rows.cpp) · [Recorded rows](binary-verification.txt) · [Independent checks](check.py) · [Recorded checks](direct-verification.txt)

```sh
c++ -O3 -std=c++17 binary_rows.cpp -o /tmp/franel-binary-rows
/tmp/franel-binary-rows
python3 -B check.py
```

Lean 4.19 verifies the explicit congruence $F_{31}(524289)\equiv2^{33}\pmod{2^{34}}$ by kernel reduction. The definition in the theorem uses ordinary binomial coefficients. Run `lake env lean /absolute/path/to/Counterexample.lean` in a Mathlib checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. [Lean proof](Counterexample.lean)
