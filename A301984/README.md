# Record values and their first indices in OEIS A301984

Blake Stone · Proof developed with OpenAI Astra 6.2

For a positive integer $n$, let $a(n)$ be the largest $k$ for which every integer from $1$ through $k$ has its binary representation as a subsequence of the binary representation of $n$. A subsequence may skip digits and must preserve their order. The OEIS entry for A301984 gives an empirical description of the successive records and their first indices. [OEIS A301984](https://oeis.org/A301984)

**Theorem.** The successive strict record values of $a(n)$, in increasing order of $n$, are exactly the positive integers whose binary representations contain at most one zero. The first index of a record $v$ is obtained from the binary representation of $v$ by replacing each $1$ with $01$, keeping each $0$, and deleting the initial zero. These two descriptions are the positive terms of A089633 and the map A048678. [OEIS A089633](https://oeis.org/A089633) · [OEIS A048678](https://oeis.org/A048678)

For example, the record $13=(1101)_2$ first occurs at $41=(101001)_2$. The initial record pairs $(n,a(n))$ are $(1,1),(2,2),(5,3),(9,5),(10,6),(21,7),(37,11),(41,13),(42,14),(85,15)$.

## Proof

Write each binary representation as $1w$, and call $w$ its **tail**. A target $1u$ is a subsequence of a host $1w$ exactly when $u$ is a subsequence of $w$. Indeed, the leading target bit can always use the leading host bit. Ordering the integers is equivalent to ordering their tails by length first, then lexicographically with $0<1$. Write $x^h$ for $h$ copies of a bit or word $x$, allowing $h=0$. A product of $h$ mixed pairs, each either $01$ or $10$, contains every $h$-bit word by selecting one bit from each pair.

**All-ones records.** To contain every tail of length $r$, a host tail must have at least $r$ zeros and $r$ ones. At the minimum length $2r$ it has exactly $r$ of each. For $1\le i\le r$, it must contain $1^i0^{r-i}$, so at most $i$ zeros can precede its $i$-th one. The tail $(01)^r$ attains all these upper bounds. It is therefore lexicographically first among the eligible tails of length $2r$. Indeed, its $i$-th one occurs as far to the right as the bound allows, for every $i$. It contains every $r$-bit target, hence every shorter one as well, and misses the next target $0^{r+1}$. Thus it attains exactly the record with tail $1^r$. For $r=0$ the tail is empty, giving $a(1)=1$.

**Records between successive all-ones values.** To improve upon the value with tail $1^r$, a host tail must contain both $1^r$ and $0^{r+1}$. Its length is at least $2r+1$. At that minimum length it has exactly $r$ ones and $r+1$ zeros. For $0\le j\le r$, consider the target and host tails

$$
V_j=1^j0\,1^{r-j},\qquad C_j=(01)^j0\,(01)^{r-j}.
$$

The $C_j$ increase lexicographically as $j$ increases.

1. **The largest covered initial interval ends at $1V_j$.** Deleting the zero between the two strings of pairs of $C_j$ gives $(01)^r$, so all tails of length at most $r$ occur. Every tail of length $r+1$ through $V_j$ starts with $1^i0$ for some $0\le i\le j$. Match its initial ones to the ones in the first $i$ pairs of $C_j$, then use the next zero. The remaining host is $(10)^{j-i}(01)^{r-j}$, which supplies any remaining $r-i$ bits. The successor of $V_j$ is $1^{j+1}0^{r-j}$. For $j<r$, the earliest possible $(j+1)$-st one in $C_j$ follows $j+2$ zeros, so only $r-j-1$ zeros remain. For $j=r$, the target requires $r+1$ ones. In either case the successor is absent.

2. **No earlier host can improve on the preceding record.** For $j=0$ that preceding record has tail $1^r$. For $j>0$ it has tail $V_{j-1}$. Any improvement requires length at least $2r+1$ by the count above. Consider a qualifying host of exactly that length, and let $z_i$ count zeros before its $i$-th one. For $1\le i\le j$, the host must contain $1^i0^{r+1-i}$. These targets are no later than the successor $1^j0^{r+1-j}$ of $V_{j-1}$. Thus $z_i\le i$. For $j<i\le r$, the shorter target $1^i0^{r-i}$ is already required, giving $z_i\le i+1$. The first range is empty when $j=0$. In $C_j$, the counts are exactly $i$ for $i\le j$ and $i+1$ for $i>j$. Hence every one in a qualifying host lies at or to the left of the corresponding one of $C_j$. This makes $C_j$ the lexicographically first possible improvement. Fact 1 shows how far it improves.

Starting with the empty host tail, these arguments exhaust the possible records. The first improvement after the all-ones record of tail length $r$ occurs at $C_0$, then the first successive improvements occur at $C_1,\ldots,C_r$. The successor of $V_r=1^r0$ is the all-ones tail $1^{r+1}$, whose first qualifying host was determined above for $r+1$. This also covers $r=0$, when $C_0=V_0=0$.

Restoring the leading bit, the record words are $1^{r+1}$ and $1V_j$. They comprise every positive binary representation with at most one zero. Applying the stated rewriting rule gives $1(01)^r$ and $1C_j$, exactly the first host words found above. ∎
