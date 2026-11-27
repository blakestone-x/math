# Perfect mixing in increasing throwback queues

Start a queue with strictly increasing positive integers $x_0,x_1,\ldots$. At each step, move the head $x$ past the next $x$ entries. Write $r_i=x_i-i+1$. The labels through $x_n$ visit every admissible configuration exactly when

$$
\gcd(r_j,r_i-1)=1 \quad\text{for every }0\le i<j\le n.
$$

This classifies perfect mixing for increasing starting queues. Darnell and Dribus proved the consecutive case and described the general classification problem in their 2025 paper. Their placement construction and their observation of reflection symmetry for the queue starting at three are credited in the manuscript. [Journal paper, especially pp. 15–16](https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.pdf)

[Manuscript (PDF)](throwback.pdf) · [LaTeX source](throwback.tex) · [Lean return-time and mixing theorems](Periods.lean) · [Lean queue erasure and gap symmetries](QueueAndGaps.lean)

| Consequence | Result |
| --- | --- |
| Exact first returns | A two-integer recurrence gives the orbit size at every prefix, including prefixes that fail to mix perfectly. The prime prefix $(2,3,5)$ visits 9 of 36 configurations. The prefix $(1,3,4)$ visits all 18. |
| Mean positions | Uniformity on a full orbit gives a recurrence for each label's mean absolute queue position. |
| Consecutive labels starting at $m$ | With $Q(t)=t+1+\lfloor t/m\rfloor$, the $(k+1)$-st occurrence of label $m+j$ is at time $Q^{\circ j}((m+1)k)$. |
| [A357081](https://oeis.org/A357081) | The gap cycle for label $3+j$ has least period $3^j$. Removing its last gap leaves a palindrome. The theorem explains the conjectured shift of [A087165](https://oeis.org/A087165) and the record indices [A155167](https://oeis.org/A155167). |

## Verification

Lean 4.19.0 with the pinned mathlib revision verifies the queue-erasure identities, the exact return-time and capacity criterion in relative-position coordinates, the translation and reflection identities for occurrences, and the least period of the gaps. The manuscript proves the coordinate identification, the mean-position formula, and the link with the sieve.

The verifier evolves the actual positions of tracked labels for all 511 nonempty subsets of $\{1,\ldots,9\}$. It compares the full orbits with the predicted periods, counts of available steps, and full-orbit means. A separate literal queue simulation checks 96,000 moves for consecutive inputs.

```sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

[Build and check output](verification.txt) · [Related sieve manuscript](../Layman-sieve/sieve.pdf)
