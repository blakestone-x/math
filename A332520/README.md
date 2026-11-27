# Counting the fixed points in OEIS A332520 by binary length

Blake Stone · Proof developed with OpenAI Astra 6.2

Rémy Sigrist's permutation A331364 inspects the digits of a nonnegative integer in bases $2^{2^h}$ for $h=0,1,2,\ldots$. If a base has exactly two distinct nonzero digit values, the permutation swaps the two values throughout the expansion in the first such base. In every other case it fixes the integer. A332520 lists the fixed points. Sigrist's entry gives an empirical formula for how many have each positive binary length. [A331364](https://oeis.org/A331364) · [A332520](https://oeis.org/A332520)

**Theorem.** For each $k\ge0$, the number of fixed points with exactly $k+1$ binary digits is $2^{s_2(k)}$, where $s_2(k)$ counts the ones in the binary expansion of $k$. This is A001316 evaluated at $k$. [A001316](https://oeis.org/A001316)

## Proof

Choose an integer $d\ge0$ such that $2^d\ge k+1$. Represent each positive candidate with highest set bit $k$ as a binary word of exactly $2^d$ bits by adding leading zeros. At level $h$, its base-$2^{2^h}$ digits are aligned blocks of $2^h$ bits, read from the right. Padding preserves the set of its distinct nonzero digits.

**Fixed-point criterion.** A word represents a fixed point precisely when, at every level, all nonzero blocks of that size are equal. To see this, begin with the whole word as a single block. Whenever all nonzero parent blocks are equal, dividing the parents in half produces at most two distinct nonzero child blocks, the left half and the right half of their common value. Consequently, the first level encountered from the top with two or more distinct nonzero blocks has exactly two. The defining permutation then acts at some base and changes the integer, since both swapped values occur. Conversely, a word with at most one nonzero block type at every level admits no swap. Levels larger than $d$ have only one digit.

Index the bit positions from the right by $0,\ldots,2^d-1$, and write each position as a $d$-bit vector. The support of a word is its set of positions containing a one. A nonempty subcube consists of all vectors formed by independently fixing each coordinate to $0$, fixing it to $1$, or allowing either value.

**Claim.** The supports of the positive fixed points are exactly the nonempty subcubes. This follows by induction on $d$. For $d=0$, the one-bit word $1$ has the sole support in dimension zero. For $d>0$, the criterion says that the two halves of the full word are either equal and nonzero, or one is zero and the other nonzero. In each case the nonzero half satisfies the same criterion at all smaller levels, and its support is a subcube by induction. The new most significant coordinate is free when both halves are nonzero. Otherwise it is fixed according to which half is nonzero. Conversely, slicing any subcube along this coordinate gives exactly those possibilities. The equal or zero halves therefore meet the block criterion at every level.

A word has $k+1$ binary digits exactly when its greatest support index is $k$. In a subcube, the greatest index has value $1$ in every free coordinate and the prescribed value in every fixed coordinate. Thus every zero bit in $k$ must be fixed to zero. Each one bit can independently be fixed to one or left free. All these choices are distinct and give maximum $k$. There are $2^{s_2(k)}$ of them, as claimed. ∎

For example, take $k=5=(101)_2$. The four possible supports are $\{5\}$, $\{4,5\}$, $\{1,5\}$, and $\{0,1,4,5\}$. The corresponding six-bit fixed points are $32,48,34,51$.

## Relation to earlier observations

A332520 already states the equal-nonzero-block criterion. Sigrist also connected these fixed points with single product terms in Boolean disjunctive normal form in A344339, which is the subcube interpretation used here. The proof derives the precise count for each largest support index directly from the defining permutation. [A332520](https://oeis.org/A332520) · [A344339](https://oeis.org/A344339)
