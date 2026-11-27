# Which throwback queues are recurrent?

**Blake Stone mathematics repository · Proof developed with OpenAI Codex.**

Start with any infinite ordering of distinct positive integers. Record the head $x$ and move it to position $x$, counting from zero. The recorded word is recurrent if and only if **every label starts at a position at most its value**. In that case every finite block recurs with bounded gaps. If a label starts too far back, the prefix ending at its first appearance occurs exactly once.

Darnell and Dribus proved uniform recurrence for increasing inputs and asked for limiting average positions for arbitrary inputs. This manuscript classifies all starting orders, gives the full limiting position distribution of every label, and proves that every finite block has a rational limiting frequency. [Original paper, Theorems 2 and 7 and Section 7](https://cs.uwaterloo.ca/journals/JIS/VOL28/Dribus/dribus4.pdf) · [Earlier increasing-queue result](../Throwback-mixing/README.md)

**Why order matters.** Use the label set $2,4,5,6,\ldots$. Starting with $(2,4,5,6,\ldots)$ gives label 4 a mean position of $13/6$. Swapping 4 and 5 at the start changes its mean to $7/3$. The manuscript's distribution formula distinguishes the two six-step orbits.

[Manuscript (PDF)](arbitrary-queues.pdf) · [LaTeX source](arbitrary-queues.tex) · [Lean proof](ArbitraryQueues.lean) · [Exact verifier](verify.py)

Lean proves the recurrence equivalences, the unique-prefix obstruction and the first-visit theorem from the position update, the head identity, positive labels and occupancy of every slot. The distribution theorem and the block-frequency result are proved in the manuscript. The verifier compares the distribution formula at all 17,006 admissible starting states over nonempty subsets of $\{1,\ldots,7\}$ and exercises 720 literal permuted queues.

```sh
lake exe cache get
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

[Verification output](verification.txt)
