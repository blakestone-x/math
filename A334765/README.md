# The longest consecutive run in OEIS A334765

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

Let $w(n)$ count the ones in the binary expansion of $n$, and let $B(n)$ sum its balanced-ternary digits, each in $\{-1,0,1\}$. Thomas König conjectured in 2020 that four consecutive nonnegative integers cannot all satisfy $w(n)=-B(n)$. [OEIS A334765](https://oeis.org/A334765)

**Theorem.** The maximum run length is three.

**Proof.** Since every power of three is odd, $B(n)\equiv n\pmod 2$. Every member therefore satisfies $w(n)\equiv n\pmod 2$. Suppose four consecutive integers qualified.

*Odd start.* Of the first and third integers, exactly one is $x=4q+1$. Its successor is also in the run. The two have the same binary weight, since $w(4q+1)=w(q)+1=w(4q+2)$. Their opposite parities contradict the necessary condition.

*Even start.* For an even $x$, passing to $x+1$ increases $w$ by one. If both qualify, $B$ must decrease by one. A final balanced-ternary digit of $-1$ or $0$ would increase by one without any carry. Thus the final digit must be $+1$, so $x\equiv1\pmod 3$. In a four-term run starting at even $n$, this argument applies to both $n$ and $n+2$. They cannot both be $1$ modulo three.

König supplied a triple attaining the bound. Here T denotes the trit $-1$.

| Integer | Balanced ternary | $B(n)$ | $w(n)$ |
| ---: | --- | ---: | ---: |
| 32,770 | 1TT0000TT01 | −2 | 2 |
| 32,771 | 1TT0000TT1T | −3 | 3 |
| 32,772 | 1TT0000TT10 | −2 | 2 |

[Proof notes, page 1](../notes/OEIS_Proof_Notes.pdf) · [Positive-sign companion, A330904](../A330904/README.md)
