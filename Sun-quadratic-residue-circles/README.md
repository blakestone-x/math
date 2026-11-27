# Circular orderings of finite-field squares

For each odd prime power $q$, let $S$ be the nonzero squares of the field of order $q$ and $T$ its nonsquares. We classify when a circle through $S$ has every element of the prescribed target class as one of its adjacent sums or ordered differences.

| Labels | Target | All field orders where no circle exists |
|---|---|---|
| Consecutive sums | Squares | 3, 5, 7, 9, 13, 25 |
| Consecutive sums | Nonsquares | 5 |
| Consecutive differences | Squares | 3, 5, 9, 25 |
| Consecutive differences | Nonsquares | 3, 13 |

At order 25 even a twelve-vertex path with distinct square-valued sums or differences is impossible. Both nonsquare targets are attained. Sun's 2019 Theorem 1.5 already proves existence for the square targets in the other field orders above thirteen. His Lemma 2.1 excludes geometric witnesses at order 25. The manuscript establishes all four failure lists and gives a generator count for geometric cycles. [Original finite-field question in A229878](https://oeis.org/A229878) · [Sun's published Theorem 1.5](https://arxiv.org/abs/1309.1679)

[Proof manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex) · [Lean certificate for order 25](Order25.lean) · [Exact classification checker](verify.py) · [Verification output](verification.txt)

The standard-library Python verifier checks 752 sign/target cases across 188 odd fields. It constructs 739 geometric circles and exhausts the path recurrence in the thirteen remaining cases. A Jacobi-sum bound proves existence for every field above this finite range.

```sh
python3 -B verify.py
lean Order25.lean
```

The Lean file uses Lean 4.19.0 with its standard library. It verifies the exponent transition tables from field arithmetic, proves exhaustive detection for every fresh-vertex/fresh-label path, and checks both nonexistence certificates by kernel reduction.
