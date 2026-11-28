# Two formulas for 123-avoiding words with three copies of each letter

Benedict W. J. Irwin conjectured an integral and a terminating hypergeometric expression for OEIS A266736 in 2016. The argument below proves both for every integer $n\ge 0$. The proof uses ordinary word RSK, the Dyck-path interpretation of Catalan numbers, and inclusion–exclusion. The enumeration of these words has an established literature. [OEIS entry](https://oeis.org/A266736) · [Balogh](https://arxiv.org/abs/1505.01389) · [Shar and Zeilberger](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/words123.html)

Let $a(n)$ count the words containing exactly three copies of each of $1,\ldots,n$ and no three positions $i<j<k$ with $w_i<w_j<w_k$. Write $C_m=\binom{2m}{m}/(m+1)$ for the Catalan numbers.

## 1. A finite Catalan sum

$$
a(n)=\sum_{j=0}^{n}(-2)^j\binom{n}{j}C_{3n-j}.
$$

**Proof.** Complement each letter $b$ to $n+1-b$. This turns avoidance of a strictly increasing triple into avoidance of a strictly decreasing triple. Ordinary row-insertion RSK now gives a pair $(P,Q)$ of the same shape with at most two rows. Indeed the number of rows equals the longest strictly decreasing subsequence length. Here $P$ is semistandard with three occurrences of each letter and $Q$ is standard. RSK is a bijection. [RSK for words of prescribed multiplicity](https://arxiv.org/abs/1505.01389)

Standardize $P$. For each letter $b$, assign the numbers $3b-2,3b-1,3b$ to its boxes from left to right. Equal entries in the bottom row occur strictly to the left of equal entries in the top row, by weak increase along rows and strict increase down columns. Encode a standard two-row tableau by reading its entries in numerical order and writing $U$ for the top row and $D$ for the bottom row. The resulting path stays at or above height zero. For the standardized $P$, each block of three steps consists of some $D$ steps followed by some $U$ steps. Equivalently, it has no adjacent $UD$ inside that block.

Conversely, recover the standard tableau from such a path by placing each number at the end of its indicated row. Merge each successive block of three labels into one letter. This preserves weak increase along rows. A repeated letter in a column would require a top-row label before a bottom-row label in that block, which the block condition forbids. Thus standardization is reversible.

Put $M=3n$. The two tableau paths have length $M$ and the same terminal height, which determines their common shape. Append the path of $Q$ in reverse order with $U$ and $D$ exchanged to the path of $P$. This gives a Dyck path of length $2M$. Cutting any such path at its midpoint reverses the construction. Hence $a(n)$ counts Dyck paths of semilength $M$ with no peak $UD$ in either of the two internal positions of each three-step block of the first half.

Use inclusion–exclusion on those $2n$ possible peaks. Requiring both candidate peaks in one block is impossible because their shared step would need to point both ways. For a compatible set of $j$ peaks, choose $j$ blocks and one of the two positions in each, in $\binom nj 2^j$ ways. The chosen pairs are disjoint. Delete them to get an arbitrary Dyck path of semilength $M-j$. Reinserting the pairs at their prescribed positions recovers the original path uniquely and preserves nonnegativity. The intersection therefore has size $C_{M-j}$. Alternating over $j$ proves the claim, including the empty word at $n=0$. ∎

## 2. Irwin's integral

The beta integral gives, for $m\ge 0$,

$$
\frac{2}{\pi}\int_0^1 \sqrt{\frac{1-t}{t}}\,(4t)^m\,dt
= \frac{2\,4^m}{\pi} B\!\left(m+\tfrac12,\tfrac32\right)
= C_m .
$$

Expand $((4t)^3-2(4t)^2)^n$ by the binomial theorem. Its term with index $j$ is $\binom nj(-2)^j(4t)^{3n-j}$. Integrating this finite expansion and applying the previous section yields

$$
a(n)=\frac{2}{\pi}\int_0^1\sqrt{\frac{1-t}{t}}\,(64t^3-32t^2)^n\,dt .
$$

The endpoint at zero is integrable even when $n=0$.

## 3. The terminating hypergeometric value

Denote the $j$-th term of the finite Catalan sum by $T_j$. Its first term is $T_0=C_{3n}$. For $0\le j<n$, use $C_{m-1}/C_m=(m+1)/(2(2m-1))$ to obtain

$$
\frac{T_{j+1}}{T_j}=
\frac{(j-1-3n)(j-n)}{(j+\tfrac12-3n)(j+1)}\,\frac12.
$$

This is the ratio of consecutive terms in the Gauss series with parameters $(-1-3n,-n;\tfrac12-3n)$ at $1/2$. The parameter $-n$ terminates it at index $n$ and its lower parameter never gives a zero denominator. The initial terms and ratios agree, proving

$$
a(n)= C_{3n}\,{}_2F_1\!\left(-1-3n,-n;\tfrac12-3n;\tfrac12\right).
$$

For example, $a(3)=C_9-6C_8+12C_7-8C_6=374$.

## Verification

[verify.py](verify.py) counts admissible words directly for $0\le n\le7$, allowing each next letter exactly when it creates no increasing triple. It also checks all 19 values displayed by OEIS and compares the finite sum, the terminating Gauss series, and a polynomial-coefficient computation using exact arithmetic through $n=100$.

Lean 4.33.1 verifies that the integral equals the finite Catalan sum and the terminating hypergeometric expression for every $n$. The axiom audit for this identity lists the standard Lean foundations only. The correspondence from words to restricted Dyck paths and the inclusion–exclusion count are proved in Section 1 of this manuscript. [Moment.lean](Moment.lean) · [Gauss.lean](Gauss.lean)

The [platform statement](OMAStatements/S_oeis_a266736.lean) defines the original word count and asks for both identities. It contains the single proof placeholder required for a Left to Solve statement submission. The two analytic proofs are independent of that placeholder. To reproduce with the pinned dependencies, run the following commands in this directory.

```sh
lake exe cache get Mathlib.Probability.Distributions.Beta Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral Mathlib.Combinatorics.Enumerative.Catalan.Basic Mathlib.Data.Fintype.Pi
lake build
python3 verify.py
```
