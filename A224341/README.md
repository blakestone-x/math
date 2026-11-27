# Two sequences that count each other's compositions

Research notes for Blake Stone. Proof developed with OpenAI Codex.

Gary W. Adamson proposed in 2013 that two integer sequences count the ordered compositions formed from each other's values, and that iterating this operation from any seed converges to the same two-cycle. Under the positive-part definition of composition, the nonconstant two-cycle exists and is unique. Its basin consists of precisely the seeds containing at least two distinct positive integer part sizes. Five displayed values in the second entry require correction. [OEIS A224341](https://oeis.org/A224341) · [OEIS A224342](https://oeis.org/A224342)

## The transform

For a set $S$ of positive integers let $c_S(n)$ count ordered lists of elements of $S$ summing to $n$. Repetitions are allowed. Splitting off the last part gives

$$
c_S(0)=1,\qquad c_S(n)=\sum_{\substack{s\in S\\s\le n}}c_S(n-s),\qquad
R(S)=\{c_S(n)\mid n\ge1,\ c_S(n)>0\}.
$$

The empty list supplies the initial condition at weight zero. The outputs used as part sizes come from positive weights. For a seed given as a sequence of real numbers, take its set of positive integer values. Convergence of supports means eventual agreement about every bounded range of part sizes.

**Theorem.** The fixed supports are $\varnothing$ and $\{1\}$. There is exactly one cycle of length two and there are no longer cycles. Every seed with at least two distinct parts converges to that two-cycle, with the order of its two phases determined by the seed. Every singleton maps to $\{1\}$.

## Entry into the two phases

The empty support maps to itself. With the single part $d$, the only positive counts are ones at multiples of $d$. Thus $R(\{d\})=\{1\}$. In particular the example seed $(1,0,0,\ldots)$ in the entries stays at this fixed support.

Suppose $S$ has distinct parts $a,b$. Its least part has count one. At weight $t(a+b)$, permuting $t$ copies of each of $a,b$ gives at least $\binom{2t}{t}$ distinct lists. Thus $R(S)$ contains $1$ and a value larger than $1$. If $b'$ is its least value larger than $1$, exactly two lists of its parts sum to $b'$: the singleton and the list of ones. Hence $R^2(S)$ contains $1,2$.

The class of supports containing $1,2$ is invariant under $R$. Within this class $c_S(1)=1$, $c_S(2)=2$ and $c_S(n+1)\ge c_S(n)+c_S(n-1)$ for $n\ge1$. The counts are strictly increasing for positive weights and $c_S(n)\ge F_{n+1}$, where $F_0=0,F_1=1$. At weight three the count is $3+\mathbf1_{\{3\in S\}}$, and at every later weight it is at least five. Consequently $3$ belongs to exactly one of $S$ and $R(S)$.

## Why every finite prefix stabilizes

Suppose two supports containing $1,2$ agree through $M\ge3$. They give the same counts through weight $M$. Counts at weights $M+1$ and higher are at least $F_{M+2}$. Their images therefore agree through

$$
f(M)=F_{M+2}-1>M.
$$

For $S$ in the invariant class, $S$ and $R^2(S)$ agree through three. Applying this observation $j$ times shows that $R^j(S)$ and $R^{j+2}(S)$ agree through $f^j(3)$. These bounds tend to infinity. Thus both the even and the odd iterates stabilize on every finite interval. The same agreement argument applies to any two initial supports in the same phase, so their phase limits coincide. The transform respects these limits by the same prefix bound. The two limits map to one another, and exactly one contains three. A periodic orbit in either phase must already equal its alternating limit on every finite interval. This proves all the assertions about supports. Because the counts depend only on part sizes up to their weight, convergence of the corresponding composition counts holds term by term. ∎

## Identification and corrections

Write $A$ for the limiting support without $3$ and $B$ for the one with $3$. Then $A$ is the range of the strictly increasing counts $c_B(1),c_B(2),\ldots$, and $B$ is the range of $c_A(1),c_A(2),\ldots$. The agreement bounds begin $3,4,7,33$. Thus a few applications of the recurrence already determine every relevant part size for the displayed terms. Through weight 20 the two sets of allowed parts are

$$
A\cap[1,20]=\{1,2,4,7,13\},\qquad B\cap[1,20]=\{1,2,3,6,10,18\}.
$$

All 19 displayed terms of A224341 agree with $c_B(n)$ at weights $1$ through $19$. Its OEIS index is one less than the weight. The first 15 displayed terms of A224342 agree with $c_A(n)$, whose weight equals the OEIS index.

| Weight $n$ | A224342 as listed | $c_A(n)$ |
|---:|---:|---:|
| 16 | 5604 | 5603 |
| 17 | 9949 | 9947 |
| 18 | 17661 | 17656 |
| 19 | 31352 | 31342 |
| 20 | 55657 | 55635 |

The first discrepancy can be checked directly from the two entries. Splitting a composition of 16 according to whether its last part is $1,2,4,7,$ or $13$ gives $3157+1778+564+101+3=5603$. The following four corrections use the same recurrence.

## Growth of the corrected pair

For $S=A$ or $B$ put $D_S(z)=\sum_{s\in S}z^s$. The counting recurrence gives $\sum_{n\ge0}c_S(n)z^n=1/(1-D_S(z))$. There is a unique $\rho_S\in(0,1)$ with $D_S(\rho_S)=1$, since the series increases from zero and includes $z+z^2$. Its derivative there is positive. On $|z|=\rho_S$, an additional zero of $1-D_S(z)$ would require all terms to lie on the positive real axis by equality in the triangle inequality, forcing $z=\rho_S$ since $1\in S$. There are no zeros inside the circle. Analyticity in the unit disk and isolation of zeros now give a radius $r>\rho_S$ with $r<1$ for which removing the simple pole leaves a function analytic on $|z|\le r$. Hence

$$
c_S(n)=\frac{\rho_S^{-n}}{\rho_S D_S'(\rho_S)}+O(r^{-n}).
$$

The limiting successive-term ratios for A224341 and corrected A224342 lie, respectively, in $(1.868875627763,1.868875627764)$ and $(1.775111889096,1.775111889097)$. The verifier uses the proved support through 150 and bounds its omitted series by $z^{151}/(1-z)$ at exact rational endpoints. [Reproduce the term and growth checks](verify.py)
