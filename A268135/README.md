# An explicit family for the proper-divisor question in OEIS A268135

Blake Stone · Proof developed with OpenAI Codex

Let $s(n)$ be the sum of the decimal digits of $n$. In 2016 Chai Wah Wu asked whether infinitely many positive integers $n$ ending in a nonzero digit have $s(n^2)$ as a proper divisor of $s(n)$. The affirmative answer already follows from a theorem of John Charles Saunders. The construction below exhibits an infinite family with both digit sums fixed. [OEIS A268135](https://oeis.org/A268135) · [Saunders, *Sums of Digits in q-ary Expansions*, Theorem 5](https://arxiv.org/pdf/1311.0515)

**Proposition.** For every integer $j\ge12$, let $n_j=448999(10^j+1)$. Then $n_j$ ends in nine, $s(n_j)=86$, and $s(n_j^2)=43$.

**Proof.** Set $a=448999$. Direct multiplication gives the following values.

| Quantity | Decimal value | Digit sum |
|---|---:|---:|
| $a$ | $448999$ | $43$ |
| $a^2$ | $201600102001$ | $13$ |
| $2a^2$ | $403200204002$ | $17$ |

In base $10^j$, the digits of $n_j$ are $a,a$, and the digits of its square are $a^2,2a^2,a^2$, because
$$
n_j^2=a^2 10^{2j}+2a^2 10^j+a^2.
$$
Each coefficient is strictly less than $10^{12}\le10^j$. Thus the corresponding blocks of $j$ decimal places are disjoint, including at $j=12$. Adding their decimal digit sums gives
$$
s(n_j)=43+43=86,\qquad s(n_j^2)=13+17+13=43.
$$
The integers $n_j$ strictly increase with $j$ and all end in the last digit of $448999$. This proves the proposition. ∎

For example, at $j=12$ the two base-$10^{12}$ blocks of $n_j$ read $448999\mid000000448999$. Its square has the three decimal blocks $201600102001\mid403200204002\mid201600102001$.

## Why the existence question was already settled

Theorem 5 of Saunders states that for every base $q\ge2$ and every rational $r$ with $0<r<1$ there is a positive integer $u$ with $s_q(u^2)/s_q(u)=r$. Take $q=10$, and for each integer $d\ge2$ use $r=1/d$. Remove all trailing decimal zeros from $u$ to obtain $v$. The digits removed from $u$ and $u^2$ are zeros, so the two digit sums and their ratio are unchanged. Different $d$ yield different ratios and hence different $v$. This proves Wu's infinitude statement using a result available before the question appeared. The explicit family above gives the additional condition that the pair of digit sums stays at $(86,43)$. [Saunders, Theorem 5, §3.1](https://arxiv.org/pdf/1311.0515) · [OEIS entry history and attribution](https://oeis.org/A268135/internal)
