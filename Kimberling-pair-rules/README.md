# Two binary replacement rules from Kimberling's conjectures

**Blake Stone mathematics repository · Proof developed with OpenAI Codex.**

Start with `00` and replace nonoverlapping pairs `00` by `001`, scanning from the left. The two rules below differ in the image of `1`. Their gaps between consecutive ones have three possible lengths, which gives a finite description of both rules, including their right endpoints. The questions were recorded by Clark Kimberling in 2017.

| OEIS entry | Result |
| --- | --- |
| [A285665](https://oeis.org/A285665) | For `1 → 000`, the length of the literal iterate satisfies the proposed order-seven recurrence for all indices. |
| [A285666](https://oeis.org/A285666) | For `1 → 010`, the lengths are [A001590](https://oeis.org/A001590) shifted by four. They start $2,3,6,11,20,37$. The listed [A001580](https://oeis.org/A001580) gives $8$ at index 2. |
| [A285667](https://oeis.org/A285667) and [A286058](https://oeis.org/A286058) | Both position limits and both all-index inequalities hold. The zero and one limits are approximately $1.419643$ and $3.382976$. |
| [A285432](https://oeis.org/A285432) | The zero-position limit is approximately $1.256431$, and the proposed strict inequality holds at every index. |
| [A285564](https://oeis.org/A285564) | The one-position limit is approximately $4.899688$. The proposed two-sided bound holds exactly for $n\ge2$. Its lower bound fails at $n=1$, where the first one is at position 3. |

The manuscript gives exact cubic-algebraic expressions for all four limits and proves the bounds for every claimed index. Its sources include [A286939, the second word](https://oeis.org/A286939), earlier numerical morphism matches for [A286058 in Sequence Machine](https://sequencedb.net/index.html?p=600&s=diff), and the [pinned OEIS data snapshot](https://github.com/oeis/oeisdata/tree/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq).

[Manuscript (PDF)](pair-rules.pdf) · [LaTeX source](pair-rules.tex) · [Lean proofs of the length recurrences](PairRules.lean) · [Independent verifier](verify.py)

Lean starts from literal lists of bits and proves both length recurrences for every iterate. It also verifies the gap substitutions and finite suffix transitions. The independent verifier compares direct replacements with the gap construction through 23 iterations, covering 2,145,013 letters for one rule and 829,009 for the other.

```sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

[Verification output](verification.txt)
