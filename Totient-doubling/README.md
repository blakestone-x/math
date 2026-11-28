# Doubling pairs in inverse totient fibers

Blake Stone · Proof developed with OpenAI Codex

Write $\mathcal V$ for the positive values of Euler’s totient. Exactly the members of $\mathcal V\setminus2\mathcal V$ have complete inverse images that can be partitioned into pairs $(x,2x)$. Every odd inverse pairs with its double. The obstruction is an inverse divisible by four, which exists precisely when half the target is itself a totient. [Manuscript (PDF)](totient-fibers.pdf) · [LaTeX source](totient-fibers.tex) · [Pairing criterion in Lean](Fibers.lean)

Torlach Rush proposed an even-sized fiber with every odd inverse in the lower half of the sorted list. The target $4$ satisfies this condition. Its full fiber is $5,8,10,12$, leaving $8$ and $12$ unmatched. The entry’s PARI program tests equality of the **numbers** of odd and even inverses, which the theorem proves equivalent to pairing. [Original entry, A376927](https://oeis.org/A376927)

## First totients on doubling rays

For each odd $s$ occurring as the odd part of a totient, exactly one of the targets $s,2s,4s,\ldots$ is paired. It is the first totient on the list. Every later target is a totient as well.

For a prime $r>3$ and $m\ge1$, $2r^m$ is a totient precisely when $2r^m+1$ is prime. For odd part $5^m$ this decides the paired value completely, since $4\cdot5^m=\varphi(5^{m+1})$ is always attained. In particular $4\cdot5^{2j}$ is paired for every $j\ge1$. The manuscript also gives a classification for arbitrary prime odd parts and an exact recurrence for fiber cardinalities. [Prime-power criteria in Lean](PrimePowers.lean)

## Verification

```sh
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

The audit constructs complete fibers for every positive target through 100,000, with a proven finite limit on the possible inverses. It finds 9,692 paired targets and reproduces the 56 published terms through 372. [Verification record](verification.txt) · [Audit code](verify.py)
