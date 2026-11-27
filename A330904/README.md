# The longest consecutive run in OEIS A330904

**Blake Stone** · Proof developed with OpenAI Astra 6.2.

Let $s_2(n)$ count the ones in the binary expansion of a nonnegative integer $n$. Let $t(n)$ be the sum of the digits in its balanced-ternary expansion, whose digits are $-1,0,1$. OEIS A330904 consists of the integers for which $s_2(n)=t(n)$. In 2020 Thomas König gave four consecutive members and conjectured that a run of five is impossible. [OEIS A330904](https://oeis.org/A330904)

**Theorem.** The maximum length of a run of consecutive integers in A330904 is four.

## Proof

Write $n=\sum_j d_j3^j$ in balanced ternary. Every power of three is odd, so

$$
t(n)=\sum_jd_j\equiv n\pmod 2.
$$

Consequently every member of A330904 satisfies $s_2(n)\equiv n\pmod 2$.

For any nonnegative integer $k$, appending the binary suffix $01$ or $10$ to $k$ adds exactly one set bit. Thus

$$
s_2(4k+1)=s_2(k)+1=s_2(4k+2).
$$

The two inputs have opposite parity. Their common binary digit sum can therefore have the required parity for at most one of them. Among the first four integers of any five consecutive integers there is one congruent to $1$ modulo $4$. Its successor is still in the block, so the block contains a complete pair $4k+1,4k+2$. This proves the upper bound.

König's example attains it. Read each row from the most significant digit to the least, with **T** denoting the trit $-1$.

| Integer | Binary | Balanced ternary | Both digit sums |
| ---: | --- | --- | ---: |
| 1026 | `10000000010` | `111T000` | 2 |
| 1027 | `10000000011` | `111T001` | 3 |
| 1028 | `10000000100` | `111T01T` | 2 |
| 1029 | `10000000101` | `111T010` | 3 |

## Verification and related work

The Lean theorem `A330904.longest_run` proves both that a run of four exists and that every run has length at most four. It computes both digit sums directly, including the carry when a balanced-ternary digit is $-1$. To check the theorem with the pinned Lean 4.35.0 toolchain, run the following from the repository root. It uses the bundled standard library. [Lean proof](Solution.lean) · [One-page PDF](A330904_proof.pdf)

```sh
cd A330904
lake build
lake comparator
```

The parity step also applies to digit sums in any odd base. Lukas Spiegelhofer recorded the analogous bound for ordinary ternary digit sums in the remarks following his introduction, on page 4 of the preprint. [Spiegelhofer, *Collisions of digit sums in bases 2 and 3*](https://arxiv.org/pdf/2105.11173#page=4)

## Palomar statement

The compared theorem is `A330904.sharp_run_bound`. The statement includes the explicit starting value 1026 and proves the bound for every starting value and run length. [Statement](Challenge.lean) · [Proof](Solution.lean) · [Provenance and AI credits](formalization.yaml)

Blake Stone licenses this submission under CC BY 4.0. [License](../LICENSE)
