# A greedy digit-length sequence visits every nonnegative integer

**Blake Stone · Proof developed with OpenAI Codex.**

Francesco Di Matteo starts with $0$. If the current number has $d$ decimal digits, the next term is the least unused nonnegative integer whose decimal expansion contains the expansion of $d$ as a contiguous substring. Di Matteo conjectured in 2016 that this gives a permutation of the nonnegative integers. We prove it in every integer base $b\ge2$, using standard expansions without leading zeros and writing zero with one digit. [OEIS A269631](https://oeis.org/A269631)

**Theorem.** Every nonnegative integer occurs exactly once. For $k\ge2$, the number $k$ occurs by position $b^{k-1}+2$, counting the initial zero as position one.

**Proof.** Suppose the largest digit length seen so far is $M$ and the current term has length $d$. Write $d$ in base $b$ and append zeros until the result has length $M+1$. This is possible because $1\le d\le M$ and $d$ itself has at most $d$ digits. The resulting numeral contains $d$ and is longer than every term so far. It supplies an unused legal choice. The greedy choice, being no larger, has length at most $M+1$.

Thus the sequence continues indefinitely, and its running maximum digit length increases by at most one per step. Since the terms are distinct and only finitely many numerals have bounded length, the maximum is unbounded. Starting at one, it must reach each positive length $k$.

Immediately after the first term of length $k$, the rule asks for the least unused integer containing the base-$b$ expansion of $k$. The smallest integer of all containing that expansion is $k$ itself. A shorter numeral cannot contain it, and an equally long numeral containing it must be identical. So $k$ has either appeared already or is chosen at this next step. This covers every positive integer, and zero was the initial term.

Finally, for $k\ge2$ there are just $b^{k-1}$ nonnegative integers with fewer than $k$ digits. Distinctness forces the first term of length at least $k$ by position $b^{k-1}+1$, and the no-skipping argument says that term has length exactly $k$. The claimed position bound follows. $\square$
