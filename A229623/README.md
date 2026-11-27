# Palindromes separated by their digit sum

Derek Orr conjectured that A229623 has $a(n)=10^{n-18}+1$ at every index $n>20$. A comparison of neighboring palindromes proves this. In decimal, the only qualifying palindrome of each length $L\ge4$ is $10^{L-1}+1$. In base $b$ the corresponding family is $b^{L-1}+1$. Odd bases also have a second family with both outer digits equal to $(b+1)/2$. These lists cover every base from length six onward. [A229623](https://oeis.org/A229623)

For addition, the same gap formula gives all decimal palindromes of at least four digits whose digit sum can be added to produce another palindrome. The qualifying numbers occur in groups of 9, 90, 900 and so on, separated by long intervals. With $A(X)$ the count up to $X$, the lower and upper limits of $A(X)/\log_{10}X$ are $9/110$ and $9/11$. T. D. Noe previously gave an infinite family contained in the classification. [A229622](https://oeis.org/A229622)

[Manuscript](palindrome-gaps.pdf) · [LaTeX source](palindrome-gaps.tex) · [Enumeration and construction checks](verify.py)

Run `python3 verify.py`. It enumerates palindromes in bases 2 through 12 and tests all 999 addition witnesses in the first three groups.
