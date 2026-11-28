# Sigrist’s prime-factor permutations

Blake Stone · Proof developed with OpenAI Codex

Start with 1. After $x$, choose the least unused positive $y$ for which $xy$ has at least $k$ distinct prime factors. Rémy Sigrist conjectured in 2017 that the resulting permutation satisfies $d_k(n)\sim n$ for every fixed $k$. [Original conjecture, A285655](https://oeis.org/A285655) · [Threshold five, A285487](https://oeis.org/A285487)

For every fixed $k$, there is a constant $P_k$ such that $|d_k(n)-n|\le P_k$ at every position. Moreover, the proportion of fixed positions among $1,\ldots,N$ tends to one. These two statements, the ratio limit, and the permutation property have Lean proofs. [Manuscript (PDF)](prime-permutations.pdf) · [LaTeX source](prime-permutations.tex) · [Bounded displacement and ratio](Sigrist.lean) · [Fixed-point density](Density.lean)

## How the walk returns to its natural order

The proof constructs a periodic set of integers with at least $k$ distinct prime divisors occupying more than half the residue classes. Each is eligible after any term. Among these integers an entire arithmetic progression consists of positions $r$ where the walk has used exactly $1,\ldots,r-1$ and next chooses $r$. The intervals between consecutive such positions are permuted internally. [Periodic sieve](Sieve.lean) · [Exact cuts](Cuts.lean) · [Greedy rule](Walk.lean)

## Moved positions

| Threshold | Conclusion in the manuscript |
| --- | --- |
| $k=2$ | The only moved positions are 2 through 6. |
| $k=3$ | At most $O(\log X)$ positions move through $X$. Eventual equality with the identity is equivalent to finiteness of both the Mersenne and Fermat prime sets. |
| $k\ge5$ | At least a constant times $X/(\log X)^2$ positions move through large $X$. The proof applies the form of Chen’s sieve recorded by Granville. |

These refinements have written proofs in Section 4. The density-one conclusion is consistent with the long early gaps in the fixed points of A285655.

## Verification

Run the pinned Lean 4.19.0 package and the standard-library Python audit from this directory.

```sh
lake build
python3 verify.py
sha256sum -c SHA256SUMS
```

The audit reconstructs 7,000 terms at each of six thresholds, reproduces the reference data, and checks the exact-cut construction on 3,392 periodic graphs. [Verification record](verification.txt) · [Audit code](verify.py)
