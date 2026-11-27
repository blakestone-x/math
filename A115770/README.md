# A run-length criterion for two families of carryless products

**Blake Stone · Proof developed with OpenAI Codex.**

Write $C(u,n)$ for multiplication of the binary coefficient polynomials over $\mathbb F_2$, with the product's bits then read as an integer. Equivalently, $C(u,n)$ is the bitwise XOR of the copies of $n$ shifted by the positions of the ones in $u$. The OEIS records conjectured equivalences for two pairs of such multipliers. TrureTuring has already proved each of these two equivalences separately using finite-state arguments. The theorem below puts both in one infinite family and describes the common solution sets directly. [A115770](https://oeis.org/A115770) · [A115801](https://oeis.org/A115801) · [Prior proof for the first pair](https://www.trureturing.org/research/oeis-a115770-carryless-seven-five-equivalence/) · [Prior proof for the second pair](https://www.trureturing.org/research/oeis-a115801-carryless-multiplier-equivalence/)

**Theorem.** For integers $d\ge2$ and $n\ge0$, the following are equivalent.

1. $(2^d-1)n=C(2^d+3,n)$.
2. $(2^{d-1}+1)n=C(2^d+2^{d-1}+1,n)$.
3. After removing trailing zeros from the binary representation of $n>0$, every remaining run of equal bits has length at least $d$. For $n=0$, take this condition to hold.

In particular, $d=3$ gives the multipliers $(7,11)$ and $(5,13)$ in A115770. Taking $d=4$ gives $(15,19)$ and $(9,25)$ in A115801. The solution sets decrease with $d$. For example, $d=5$ gives $(17,49)$ in the second identity, so A115809 is contained in A115801. [A115809](https://oeis.org/A115809)

## Transitions and parity

Let $b_i$ be the bit of $n$ at position $i$, extended by zero both for negative $i$ and above the highest bit. A transition occurs at $i$ when $b_i\ne b_{i-1}$. There are finitely many transitions. The gaps between successive transitions are exactly the lengths of the runs in condition 3.

For any finite set $T$ of transition positions, its gaps are all at least $d$ if and only if, for each $i\in T$, the preceding $d-1$ positions contain an even number of elements of $T$. Necessity holds because the count is zero. For sufficiency, scan from left to right. If a first gap shorter than $d$ occurs, the window ending just before its right endpoint contains its left endpoint and nothing earlier, since the previous gaps were all at least $d$. The count is one, a contradiction. Reversing the order gives the same equivalence using the *following* $d-1$ positions.

## The subtraction

Compute $2^d n-n$ by binary subtraction. Let $c_i$ be the outgoing borrow at position $i$, with $c_{-1}=0$. The output bit is $b_{i-d}\mathbin{\oplus} b_i\mathbin{\oplus}c_{i-1}$. Condition 1 prescribes output bit $b_{i-d}\mathbin{\oplus}b_i\mathbin{\oplus}b_{i-1}$, hence it is equivalent to $c_i=b_i$ for every $i\ge0$.

Substitute those proposed borrows into the update rule. From a minuend bit $b_{i-d}$ we subtract $b_i+b_{i-1}$. If both subtracted bits are zero the outgoing borrow is zero, and if both are one the outgoing borrow is one. At a transition, exactly one is subtracted. The borrow is then $1-b_{i-d}$, and equals $b_i$ exactly when $b_{i-d}=b_{i-1}$. Thus the proposed borrows obey every update if and only if for each transition $i$ the preceding $d-1$ positions contain an even number of transitions. Initial borrow zero and uniqueness of the successive updates give both directions. The transition criterion proves the equivalence of conditions 1 and 3.

## The addition

Compute $2^{d-1}n+n$, and write $e_i$ for the outgoing carry at position $i$, with $e_{-1}=0$. Comparing the ordinary output bit $b_{i-d+1}\mathbin{\oplus}b_i\mathbin{\oplus}e_{i-1}$ with the required carryless output bit shows that condition 2 is equivalent to $e_i=b_{i-d+1}$ for all $i\ge0$.

Set $j=i-d+1$. With the proposed carries, the three bits added at position $i$ are $b_j,b_i,b_{j-1}$. Their majority is the outgoing carry, which must be $b_j$. If $b_j=b_{j-1}$ this always holds. At a transition $j$ it holds exactly when $b_i=b_j$, or equivalently $b_{j+d-1}=b_j$. This says that the following $d-1$ positions contain an even number of transitions. Positions with negative $j$ impose no further condition. The reversed transition criterion and uniqueness of carries now give the equivalence of conditions 2 and 3. ∎

## Counting by bit length

Let $c_d(L)$ count positive solutions of binary length $L$. The generating function for the length of a run of at least $d$ bits is $R=x^d/(1-x)$. After the trailing zeros are removed, a permitted word begins and ends with one, so its number of runs is odd and its successive run lengths determine it uniquely. Appending an arbitrary number of trailing zeros gives

$$
\sum_{L\ge1} c_d(L)x^L
=\frac{1}{1-x}\frac{R}{1-R^2}
=\frac{x^d}{(1-x)^2-x^{2d}}.
$$

For $n=455=(111000111)_2$ the shortest run has length three. It therefore satisfies both identities for $d=3$ and neither for $d=4$.
