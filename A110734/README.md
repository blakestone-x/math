# A common infinite family of zeros for two digit-insertion sequences

Blake Stone · Proof developed with OpenAI Astra 6.2

**Theorem.** For every $r\ge1$, both OEIS A110734 and A110735 are zero at $n=100^r+1$. The first three common counterexamples in this family are $101$, $10001$, and $1000001$.

In A110734 one inserts exactly one decimal digit into every internal gap of $n$ and looks for a multiple of $n$. In A110735 one also inserts a digit at each end, with the new leading digit nonzero. Each sequence records the smallest resulting multiple or zero if there is none. In 2005, Amarnath Murthy conjectured eventual positivity for A110734 and positivity at every index for A110735. The theorem disproves both. [A110734](https://oeis.org/A110734) · [A110735](https://oeis.org/A110735)

## The obstruction at 101

With end insertions, every candidate has the form $\overline{a1b0c1d}$. Since $100\equiv-1\pmod{101}$, its residue is represented by

$$
20-a+b-c+d.
$$

This integer lies between $2$ and $38$, even if the leading digit $a$ may be zero. Thus no assignment gives a multiple. An internal-only multiple would also give an assignment in this enlarged search: prepend and append zeros, multiplying the candidate by ten.

## Proof for every index in the family

Write $x=100$ and $n=x^r+1$. The decimal expansion of $n$ is a $1$, then $2r-1$ zeros, then another $1$. Insert one digit in every gap and at both ends. Allow the first inserted digit to be zero. Every resulting value is

$$
N=10(x^{2r}+1)+\sum_{i=0}^{2r+1} e_i x^i,
\qquad 0\le e_i\le9.
$$

The fixed ones contribute the first term. The inserted digits occupy the even powers of ten, which are exactly the powers of $x$ shown in the sum.

Modulo $n$ we have $x^r\equiv-1$. Collect the terms with exponents congruent to $j\bmod r$. This gives the integer representative

$$
W=20+\sum_{j=0}^{r-1} c_j x^j,
\qquad
c_j=\sum_{\substack{\ell\ge0\\j+\ell r\le2r+1}}(-1)^\ell e_{j+\ell r}.
$$

Each coefficient is an alternating sum of at most four digits, with at most two of either sign. Thus $-18\le c_j\le18$. The constant term satisfies

$$
2\le 20+c_0\le38.
$$

Since all higher powers of $x$ are multiples of $100$, this shows $W\ne0$. At the same time,

$$
|W|\le20+18\frac{100^r-1}{99}<100^r+1=n
\qquad(r\ge1).
$$

The only multiple of $n$ strictly between $-n$ and $n$ is zero. Hence $n\nmid W$ and $n\nmid N$. This proves the A110735 claim even with a leading zero allowed. For any candidate $M$ in A110734, prepend and append zero digits to obtain one of these enlarged candidates, of value $10M$. If $n\mid M$, then $n\mid10M$, a contradiction. Since $100^r+1$ grows without bound, eventual positivity fails as well. $\square$

**Other bases.** The same proof works in every integer base $b\ge4$ at $n=b^{2r}+1$. Set $x=b^2$. The representative has constant contribution $2b$ and $|c_j|\le2(b-1)$. Its constant coefficient lies in $[2,4b-2]$, strictly below $b^2$. Its absolute value is at most $2b+2(b-1)(x^r-1)/(x-1)<x^r+1$. The latter bound holds first at $r=1$ and then for all larger $r$ because $2(b-1)/(x-1)=2/(b+1)<1$.

## Exactly which repeated end digits work?

For $x=100$, $r\ge1$ and a decimal digit $d\in\{1,\ldots,9\}$, consider $n=d(x^r+1)$, whose first and last digits are both $d$ and whose other digits are zero. **Both insertion rules admit a multiple exactly when $d=5$.**

Indeed, every multiple of $n$ is a multiple of $x^r+1$. Reducing modulo the latter as before gives $W_d=20d+\sum c_j x^j$ with $|c_j|\le18$. For $d\ne5$ the interval $[20d-18,20d+18]$ contains no multiple of $100$, so $W_d\ne0$. For $r\ge2$,

$$
|W_d|\le180+18\frac{x^r-1}{99}<x^r+1.
$$

For $r=1$, $W_d$ itself lies in $[20d-18,20d+18]$. This interval lies in $[2,98]$ for $d\le4$ and in $[102,198]$ for $d\ge6$, so it contains no multiple of $101$. This excludes both rules for every $d\ne5$.

For $d=5$, the internal-gap witness is

$$
M=5(x^r+1)^2=5(x^{2r}+1)+10x^r.
$$

The term $10x^r$ fills one internal gap with $1$; all the other gaps contain zeros. For the end-insertion rule, take

$$
10M+x^{r+1}(x^r+1)
=50(x^{2r}+1)+2x^{r+1}+x^{2r+1}.
$$

Here the original digits $5$ contribute $50(x^{2r}+1)$, the new leading digit is $1$ and the only other nonzero inserted digit is $2$. Both summands on the left are divisible by $5(x^r+1)$, since $5\mid x$. For example, at $n=505$ the two witnesses are $51005$ and $1520050$.
