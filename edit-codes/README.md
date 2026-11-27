# An exact family of quaternary edit codes

**Blake Stone · Proof developed with OpenAI Codex.**

Let $E_q(n,d)$ denote the largest size of a set of length-$n$ words on $q$ symbols with pairwise Levenshtein distance at least $d$. Each insertion, deletion or substitution costs one.

**Theorem.** For all integers $r\ge1$ and $0\le s<r$,
$$
E_4(7r-s,6r-s)=8.
$$

In particular, the maxima at $(n,d)=(13,11)$ and $(14,12)$ are both eight. At length thirteen this means one can send any of eight distinct messages and uniquely correct any five insertions, deletions or substitutions in total: two distance-five error balls cannot overlap when their centers are at distance at least eleven. The November 16, 2026 version of Abraham Yeung's table lists lower bounds of seven for both. The length-seven starting value was already known from Houghten's tables. We give explicit words, an upper bound, and code that checks each distance in the small examples. The comparisons below refer to these particular tables. [Yeung, quaternary fixed-length table](https://abrahamyeung.com/edit-codes/) · [Houghten, quaternary fixed-length table and original publications](https://cosc.brocku.ca/~shoughten/quaternaryedit.html)

## Repeating each symbol

Write $R_r(x)$ for the word formed by replacing each symbol in $x$ by $r$ consecutive copies. For words of any lengths,
$$
d_{\rm edit}(R_r(x),R_r(y))=r\,d_{\rm edit}(x,y).
$$
This identity also follows from Corollary 1 and Theorem 4 of Ingyu Baek's 2024 paper, which proves homogeneity for exponent-strings with positive real scaling. Here is a direct argument for integer repetition. [Baek, *Exponent-Strings and Their Edit Distance*](https://arxiv.org/html/2408.12931v1)

The upper bound follows by performing each edit on all $r$ copies. For the reverse bound, take an optimal alignment of the expanded words. A paired position costs zero for equal symbols and one for unequal symbols. An unpaired position costs one.

Create a bipartite multigraph on the positions of the original two words. Each paired pair of copies gives an edge joining their original positions. The degree of every vertex is at most $r$. By the bipartite edge-coloring theorem, these edges can be colored with $r$ colors with no color repeated at a vertex. One proof pads the two vertex sets to equal size and joins deficient vertices across the two parts until the graph is $r$-regular, allowing parallel edges. Hall's theorem supplies a perfect matching. Remove it and repeat, then discard the padding edges.

Each color specifies a valid alignment of the two original words. Its edges have distinct endpoints, and they preserve order because the full alignment of copies preserves order. In the sum over colors, each paired mismatch costs one exactly once. Each original position of degree $t$ is unpaired in exactly $r-t$ colors, the number of its unpaired copies. The total cost of these $r$ alignments therefore equals the cost of the expanded alignment. Each has cost at least $d_{\rm edit}(x,y)$, proving the equality.

## Construction and optimality

Use these eight words on the alphabet $\{0,1,2,3\}$.

```text
1333310   3322223   3100111   1111022
2231133   0220000   0002332   2013201
```

Their 28 pairwise edit distances all equal six, as the [verifier](verify.py) checks by the usual edit-distance recurrence. Repeat each symbol $r$ times, then delete the first $s$ symbols from every word. Removing prefixes of length $s$ decreases pairwise distance by at most $s$. Indeed one possible alignment of the originals aligns their prefixes by at most $s$ substitutions and then aligns the two suffixes optimally. This gives eight words of length $7r-s$ with minimum distance at least $6r-s$.

Suppose there were nine such words. Edit distance is at most Hamming distance, so any pair agrees in at most $r$ coordinates. The 36 pairs have at most $36r$ agreements in total. In a single coordinate, distributing nine symbols among four possible values creates at least six agreeing pairs: the balanced multiplicities are $3,2,2,2$. Thus there are at least $6(7r-s)>36r$ agreements, since $s<r$. This contradiction proves optimality.

## Two further table bounds

A second explicit seed in the verifier has sixteen quaternary words of length four and minimum distance three, a known starting size in Houghten's table. Repeating symbols three or four times gives the bounds below. The results at length 12 and 16 in this table are lower bounds; an optimality proof for them would require an upper bound.

| Length | Minimum distance | Lower bound in Yeung's Nov. 16 table | Explicit size here |
|---:|---:|---:|---:|
| 12 | 9 | 14 | 16 |
| 16 | 12 | 13 | 16 |

Run `python3 verify.py --words` to print every codeword in all four table comparisons and recompute every pairwise distance directly. The proof of the infinite family uses the repetition identity and the nine-word counting bound.

## Variable-length codes near the maximum distance

Let $V_q(n,d)$ allow distinct words of any length from zero through $n$ over $q\ge2$ symbols. For $1\le d\le n$ there is another exact range:
$$
d>\binom{q+1}{2}(n-d)\quad\Longrightarrow\quad V_q(n,d)=q+1.
$$

**Proof.** The empty word and the $q$ constant words of length $n$ have pairwise distances exactly $n$. For the upper bound, at most one word in a code can have length less than $d$. Any two such words can be transformed into one another using at most the longer length in edits by substituting in the common prefix and then adjusting the length.

If the code had $q+2$ words, choose $q+1$ with lengths at least $d$. Count agreements among pairs in their first $d$ coordinates. Each coordinate has at least one agreement, giving at least $d$ overall. A pair agreeing $h$ times within these positions has edit distance at most $n-h$ by the same prefix alignment. Thus each pair can have at most $n-d$ agreements. The assumed strict inequality makes these two counts incompatible. $\square$

Two entries with unequal prior lower and upper bounds now coincide. The binary cell at $(12,11)$ was listed as $3$–$5$ and equals $3$. The ternary cell at $(10,9)$ was listed as $4$–$13$ and equals $4$. Both numerical upper bounds also follow from smaller exact entries already in the same tables: delete the last symbol of each nonempty word to reduce the maximum length and the required distance by one. Reattaching the two terminal symbols costs at most one edit, including when one of the original words was empty. This deletion preserves cardinality for a code of minimum distance at least two. The two shorter cells are $V_2(11,10)=3$ and $V_3(9,8)=4$. Thus these specific corrections can also be obtained directly from earlier data. The displayed general criterion is sufficient for optimality. [Yeung's variable-length tables](https://abrahamyeung.com/edit-codes/) · [Houghten's binary table](https://cosc.brocku.ca/~shoughten/binaryeditvar.html) · [Houghten's ternary table](https://cosc.brocku.ca/~shoughten/ternaryeditvar.html)
