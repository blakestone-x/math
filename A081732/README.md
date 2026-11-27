# A proof of the ternary one-edit recurrence

**Blake Stone** · Counting argument developed with OpenAI Astra 6.2.

OEIS A081732 counts the nonnegative integers whose canonical base-three numeral can be obtained from that of $n$ by exactly one insertion, deletion, or substitution. Zhuorui He added nine conjectured recurrences to the sequence on October 1, 2025. [OEIS A081732](https://oeis.org/A081732)

**Theorem.** For $n\ge9$ and $d\in\{0,1,2\}$,

$$
a(3n+d)=a(n)+
\begin{cases}
4 & d=n\bmod 3,\\
5 & d\ne n\bmod 3.
\end{cases}
$$

Setting $n=3m+i$ and $d=j$ gives all nine OEIS identities for $m\ge3$ and $i,j\in\{0,1,2\}$.

## Written proof

Let $w$ be the canonical ternary numeral of $n$, written in the usual order. Write $L$ for its length and $r$ for the number of maximal runs of equal digits. Put $\delta=1$ if its second digit is zero and $\delta=0$ otherwise. Here $L\ge3$. [One-page proof (PDF)](A081732_proof.pdf)

- Deleting digits in positions $i<j$ gives the same word exactly when every digit from $i$ through $j$ is equal. Comparing the two shifted segments proves this directly. Each run therefore gives one deletion outcome. When the second digit is zero, deleting the first digit gives a noncanonical word of length at least two. The count is $r-\delta$.
- In each insertion outcome, mark the leftmost digit whose deletion recovers $w$. The eligible positions form one run. Thus the marked digit is either first or different from its predecessor. Conversely, each insertion satisfying this condition produces one uniquely marked outcome. There are two nonzero choices at the front and two choices after each of the $L$ digits. The count is $2L+2$.
- One substitution is allowed at the first position and two at each later position. Each outcome identifies its changed position. The count is $2L-1$.

The three classes have distinct lengths, so their counts add to $a(n)=4L+1+r-\delta$. Appending $d$ increases $L$ by one, preserves $\delta$, and increases $r$ by one exactly when $d$ differs from the last digit. This proves the theorem.

## Machine-checked proof

The Lean file gives a second proof. It represents words least significant digit first, defines a one-edit relation, and enumerates exactly the canonical neighboring integers without duplicates. For a numeral of at least three digits, appending a digit carries forward its old neighbors. Four new outputs come from two substitutions and two insertions. Deleting the appended digit contributes a fifth output exactly when adjacent digits differ. [Lean source](Solution.lean)

| Lean theorem | What it verifies |
| --- | --- |
| `integerNeighbors_spec` | An integer is in the enumeration exactly when its numeral is one edit from the input. |
| `integerNeighbors_nodup` | Every neighboring integer occurs once. |
| `recurrence` | The stated identity holds for every integer $n\ge9$ and every ternary digit. |
| `nine_cases` | The nine identities follow for every $m\ge3$. |

With Lean installed through Elan, run the following from the repository root. The local toolchain file pins Lean 4.35.0. The proof uses only the bundled standard library.

```sh
cd A081732
lake build
lake comparator
```

The file checks the examples $100_3$, $1000_3$, and $1001_3$, then prints the axioms used by the four theorems.

## Attribution

Reinhard Zumkeller contributed the sequence in 2003. Zhuorui He stated the ternary recurrence in 2025. Robert Israel recorded the analogous binary recurrence in 2019. [Ternary entry](https://oeis.org/A081732) · [Binary entry](https://oeis.org/A080950)

## Palomar statement

The compared theorem is `A081732.distinct_neighbor_recurrence`. The Lean statement expresses cardinalities by duplicate-free lists characterized by the edit relation. Substituting n = 3m+i and d = j recovers the nine identities. The closed count using runs in the PDF has a separate written proof. [Statement](Challenge.lean) · [Proof](Solution.lean) · [Provenance and AI credits](formalization.yaml)

Blake Stone licenses this submission under CC BY 4.0. [License](../LICENSE)
