# Binary reverse subtraction always reaches a palindrome

Fix a width of $n$ bits, keep leading zeroes, and repeatedly subtract the reversal of the current word modulo $2^n$. **Every starting word reaches a palindrome.** The argument answers Thomas Scheuerle’s termination question for OEIS A338203. His 2020 entry reported computations through 32 bits and recorded Kevin Ryde’s suggestion to follow the central pair. [Source question](https://oeis.org/A338203) · [Row maxima](https://oeis.org/A338205)

[Proof manuscript (PDF)](manuscript.pdf) · [LaTeX](manuscript.tex) · [Lean proof](Proof.lean) · [Exact maxima and witnesses](maxima.txt)

| Result | Scope |
|---|---|
| Termination | Zero is the only cycle. At either width $2m$ or $2m+1$, the first palindrome occurs within $2^{m+1}-2$ steps. |
| Central pair | At width $2m$ the middle pair agrees within $2^m$ steps and remains equal. This proves the proposed strict bound of $2^{2m-2}$ for $m>1$, with the four-bit case checked explicitly. |
| Odd widths | Deleting the middle bit preserves the hitting time of each word, proving Scheuerle’s observation and the corresponding maximum identity. Every even-width hitting time occurs twice as often in the following odd width. |
| New table entries | At widths 32, 34, 36, 38 and 40 the exact maxima are **76, 83, 91, 113 and 115**. The same values apply to widths 33, 35, 37, 39 and 41. |

The proof tracks the two borrows around each pair of mirror positions. Along a hypothetical nonzero cycle, the innermost mismatched pair forces equal alternating borrows just outside it. Every successive pair propagates this alternation outwards. The incoming borrow at the least significant bit is always zero. A separate run-length argument bounds the time to first agreement and then removes that central pair.

## Reproduce the checks

The [Lean file](Proof.lean) uses the standard library in Lean 4.19.0. It proves `every_word_reaches_palindrome`, `zero_is_only_cycle`, the arithmetic semantics `step_mod`, and the odd-width palindrome-time correspondence. An explicit orbit starting at $2^m-1$ takes exactly $m$ steps, so the maxima tend to infinity. The manuscript proves the quantitative bound and the enumeration separately. Compile the C++ program with a C++17 compiler. Its default run stops at 12 pairs. All twenty require approximately 3.3 GiB for the largest distance array.

```sh
lean Proof.lean
python3 check.py
c++ -O3 -std=c++17 verify.cpp -o /tmp/verify-reverse-subtraction
/tmp/verify-reverse-subtraction 20 > /tmp/reverse-subtraction-maxima.txt
diff -u maxima.txt /tmp/reverse-subtraction-maxima.txt
```

The [enumerator](verify.cpp) represents a word by the $m$ signed differences between its mirrored bits. It covers exactly $3^m$ classes, including every initial word. The [independent checker](check.py) uses direct integer subtraction at every input through width 17 and replays each of the twenty extremal witnesses. The reported maxima through $m=15$ agree with the existing A338205 table.
