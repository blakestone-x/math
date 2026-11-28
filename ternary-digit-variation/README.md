# Ternary digit variation in every fixed column

Let $T,D,U$ be the sums, over consecutive base-three digits read from left to right, of the absolute changes, the drops and the rises, respectively. For $V\in\{T,D,U\}$, let $c_V(n,k)$ be the $k$-th positive integer with $V=n$, for $k\ge1$. Ordinary numerical order of these integers orders digit words first by length and then lexicographically. The entries in question are Kimberling's three arrays [A297440](https://oeis.org/A297440), [A297441](https://oeis.org/A297441), [A297442](https://oeis.org/A297442) and the proposed first columns [A297443](https://oeis.org/A297443), [A297444](https://oeis.org/A297444), [A297445](https://oeis.org/A297445).

**Theorem.** Fix a column $k$. For every $n\ge4k+12$,
$$
\begin{aligned}
c_T(n+4,k)-2c_T(n+2,k)-3c_T(n,k)&=2,\\
c_D(n+2,k)-9c_D(n,k)&=6,\\
c_U(n+2,k)-9c_U(n,k)&=2 .
\end{aligned}
$$
Consequently every column satisfies the conjectured eventual homogeneous recurrence. With $E c(n)=c(n+1)$, its polynomial is $(E-1)(E^4-2E^2-3)$ for total variation and $(E-1)(E^2-9)$ for either directional variation. The first columns are exactly A297443, A297444 and A297445, including their initial terms.

## A digit-order observation

Give an edge $a\to b$ of a digit word the nonnegative *deficit* $2-|a-b|$. Edges of deficit zero alternate between 0 and 2. In a word starting and ending with extreme digits (0 or 2), a total deficit of two has just two possible forms:

- One equal pair $00$ or $22$, with all other edges alternating.
- One internal digit 1 between extreme digits, with all other edges alternating.

Indeed, a digit 1 internal to the word already costs at least one on either side. Two adjacent 1s cost two on their common edge and would cost extra at either end of that run. Without any 1, an edge of positive deficit costs precisely two.

Consider the alternating reference word with the same starting digit and length. Replacing an expected outgoing edge of an extreme digit $a$ by $aa$ reverses the phase of all subsequent alternating digits relative to the reference. Inserting the exceptional two-edge segment $a1b$ in place of two alternating edges reverses that phase precisely when $a\ne b$. A prescribed extreme final digit determines whether the phase must reverse or be retained. With a free extreme final digit, either is allowed.

At the **first** departure below the reference word in lexicographic order, the expected digit must have been 2, preceded by 0. The possibilities, in increasing order at that position, are as follows. Each displayed string includes the preceding 0.

| Required final phase | Segments at the first departure below the reference |
|---|---|
| Reversed | $00,\ 012$ |
| Retained | $010$ |
| Free | $00,\ 010,\ 012$ |

Each choice exhausts the deficit and uniquely forces the rest of the word. Candidates first departing below the reference at an earlier position precede all those first departing below at a later one. They also precede the reference and every word whose first departure is above it. These comparisons follow by looking at the first unequal digit. We use positions with room for a full segment and a further alternating tail, so end-of-word exceptions fall after the candidates used here.

## Total variation

Suppose first that $n=2m$, with $m\ge1$. Length $m+1$ is the minimum and attains variation $2m$ only by alternating, starting with 2. At length $m+2$ there are two units of deficit. A word starting with 1 must spend one on its first edge, since a prefix 11 already costs two and its next edge costs at least one. For $m\ge2$, it must spend the remaining unit on a final digit 1, as an internal 1 costs two and a flat extreme edge costs two. The second digit can be 0 or 2, and the intermediate extrema alternate. These are ranks 2 and 3. All later candidates at this length start with 2. Their final digit is extreme, since a single terminal 1 would leave one unit which cannot be spent. Apply the free-phase row of the table to the initial 2. The first $k-3$ such candidates, if needed, thus have a fixed exceptional segment near the beginning and an alternating tail.

For $n=2m+1$, the minimum length is $m+2$, with one unit of deficit. For $m\ge1$ there are exactly three words, in order: one starting with 10, one starting with 12, and one starting with 2 and ending in 1. The rest of their digits alternate between extremes. At the next length $m+3$ there are three units of deficit. The lexicographically smallest possible two-digit prefix is 10. This spends one unit and leaves two on the path starting at its 0. As in the even case its final digit must be extreme. The free-phase row supplies any fixed number of candidates with prefix 10 once $m$ is sufficiently large. These precede every word at that length with a larger prefix.

For either parity and each fixed rank, increasing $n$ by two therefore adds one digit at the end of the growing alternating segment. This includes the explicitly listed early ranks. If the word has a final exceptional 1, the new digit is inserted immediately before that 1. Write $a_n=c_T(n,k)$ and $e_n=a_{n+2}-3a_n$. If the added digit is $d\in\{0,2\}$, appending it gives $e_n=d$. Inserting it before a final 1 gives $e_n=3d-2$, by evaluating both words in base three. In either case the next such digit is $2-d$, so $e_n+e_{n+2}=2$. This proves the first asserted identity.

## Up and down variation

For a real digit word $w$ of length $\ell$, adjoin virtual terminal digits to form $0w2$ for down-variation and $2w0$ for up-variation. The first augmented path has total drop $D(w)$ and net rise 2. The other has total rise $U(w)$ and net drop 2. Thus variation $n$ in the chosen direction is equivalent in both cases to total variation $2n+2$ of the augmented word. Its deficit equals $2(\ell-n)$, so $\ell\ge n$. Its endpoints are opposite. An undefected alternating path between them has an odd number of edges, meaning $\ell$ is even.

For **down-variation** with even $n\ge2$, length $n$ supplies one word, the real digits $2020\ldots20$. For odd $n$, length $n$ supplies none. At length $n+1$, for either parity the deficit is two. The augmented path must reverse the reference phase when $n$ is even and retain it when $n$ is odd. The smallest possible first real digit is 1. It spends all the deficit in the segment $012$ for even $n$, or $010$ for odd $n$, starting with the virtual 0. Each gives one word, after which all candidates start with real digit 2. Starting from the augmented prefix $02$, apply the appropriate row of the table. All the selected words are forced alternating near the virtual final 2, so the real word ends in 0.

For **up-variation**, length $n$ is impossible for either parity: a fully alternating path starting at the virtual 2 would begin its real digits with a forbidden leading 0. At length $n+1$ the deficit is two. For even $n$ the phase must reverse, so the augmented word starts with $210$ or $22$, and the remainder is forced. These give ranks 1 and 2 in this order. For odd $n$ the phase must be retained, so there is exactly one candidate, starting with $212$. The first real digit must be 1 or 2, and the deficit-two classification proves exhaustiveness.

At length $n+2$ for up-variation, the deficit is four. Use the lexicographically smallest possible real prefix 10. The augmented prefix $210$ spends two, leaving a path of length $n+1$ edges from 0 to the final virtual 0, with deficit two. Consequently it must reverse phase for even $n$, or retain phase for odd $n$. The table orders its first candidates, all with the chosen real prefix. For fixed $k$, these give enough candidates to precede every other prefix at this length once $n$ is large. The real word ends in 2, followed by the virtual 0.

The bound in the theorem makes all these “enough candidates” statements uniform. In every application of the table, at most two leading real digits have been fixed. Beyond the last fixed digit the reference alternates. Its $k$-th edge $0\to2$ reaches its 2 at or before real digit $2+2k$, even if the first edge after the prefix is descending. The longest exceptional segment then uses one further digit. All lengths at which the table is used are at least $\lfloor n/2\rfloor+1$; for $n\ge4k+12$ this is at least $2k+7$. Thus each of those $k$ positions leaves at least four real digits after the exceptional segment. Each position supplies at least one candidate. Their ordering and their initial segments are independent of the remaining length within the given parity of $n$.

For either direction, increasing $n$ by two lengthens the real word by two digits, preserving its prefix and the phase of its terminal alternating digits. A down-word therefore appends $20$, whose base-three value is 6. An up-word appends $02$, whose value is 2. This proves both directional identities.

## The three first columns

Let $A_j=(3^{j+1}-2-(-1)^j)/4$ for $j\ge0$. This is the value of the length-$j$ alternating word starting at 2, with $A_0=0$, as follows by summing a finite geometric progression. In each of the three arrays the first entry of row zero is 1.

For total variation the preceding minimum-length argument gives, for $m\ge1$,
$$
 c_T(2m,1)=A_{m+1},
 \qquad c_T(2m+1,1)=3^{m+1}+A_m \quad(m\ge0).
$$
For odd variation the winning word starts with 10 and then alternates. This remains valid at $n=1$, directly from the word $10$. These formulas give the initial terms $1,3,6,11,20,33$. The affinely forced identity $c_T(n+4,1)-2c_T(n+2,1)-3c_T(n,1)=2$ holds for all $n\ge1$, as follows either by appending the next alternating digit or by substitution. Taking first differences gives the defining recurrence of A297443 at every required index $n\ge6$.

For down-variation, even $n\ge2$ has least word alternating from 2 of length $n$, and odd $n\ge1$ has least word starting with 10 of length $n+1$ and continuing to alternate. This includes $n=1$, where the least word is $10$. Their values simplify to
$$
 c_D(n,1)=3^n-\frac{(-3)^n+3}{4}\qquad(n\ge1).
$$
For up-variation, at positive even $n$ the least word starts with 10, at odd $n$ it starts with 12, and both have length $n+1$ with the remaining extrema alternating. At $n=1$ the word is $12$. Thus
$$
 c_U(n,1)=\frac{6\cdot3^n-(-3)^n-1}{4}\qquad(n\ge0).
$$
The directional formulas give the initial terms $1,3,6,33$ and $1,5,11$, respectively, and satisfy the recurrence with characteristic polynomial $(E-1)(E^2-9)$ at output indices $n\ge4$ and $n\ge3$, respectively. These are exactly the first-column conjectures A297444 and A297445.

Earlier independent submissions by jleguina treated the first-column problems A297443 and A297445. The proof above derives those cases along with A297444 from the same ordering of digits used for every column. [A297443 submission, PR 16780](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16780) · [A297445 submission, PR 16784](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16784).

Each row contains infinitely many positive integers: a first-column word exists for every variation, and repeating its final digit preserves its variation. The Python checker independently ranks words, verifies 32 columns through row 160 and compares with direct enumeration through 20,000. [Verifier](verify.py) · [Total statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18227) · [Down statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18229) · [Up statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18231)
