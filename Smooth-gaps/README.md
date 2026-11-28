# Largest endpoints of signed smooth gaps

Blake Stone · Proof developed with OpenAI Codex

For a fixed set of primes, how large can a smooth positive integer be if subtracting the gap $n$ must leave a smooth nonzero integer of either sign? Zhicheng Wei gives conjectural maxima for the primes through 5 and through 7. Both displayed lists and both proposed first shortfalls follow from the coprime-triple reduction in the paper. [Gap manuscript (PDF)](smooth-gaps.pdf) · [LaTeX](smooth-gaps.tex) · [OEIS A391077](https://oeis.org/A391077) · [OEIS A376924](https://oeis.org/A376924)

| Sequence | Complete prefix | First positive value below its index | First zero | At gap 31 |
|---|---:|---:|---:|---:|
| 5-smooth, A391077 | 333,333 | $A(281)=256$ | 583 | 256 |
| 7-smooth, A376924 | 47,619 | $A(1849)=1800$ | 3,737 | 4,000 |

For every smooth $h$ in the corresponding row, $A_5(h)=81h$ and $A_7(h)=4375h$. There are also infinite families of gaps with no representation. For every $j\ge0$, $A_5(11^{4+j}h)=0$ and $A_7(11^{5+j}h)=0$.

## How often a gap occurs

For any finite nonempty prime set $S$ of size $k$, write $c_S=1/(k!\prod_{p\in S}\log p)$. The number of representable gaps through $X$ is asymptotic to $c_S^2(\log X)^{2k}$. Among these gaps the proportion with a unique representation tends to one. The largest endpoint is above the gap half the time and below it half the time in the limit.

More precisely, for either specified sign and $0\le t\le1$, a proportion tending to $t^k/2$ has that sign and $|A_S(n)-n|\le n^t$. The manuscript proves a uniform error bound and shows that all gaps with several representations form a finite union of sets $dH_S$, where $H_S$ is the set of positive $S$-smooth integers. The analytic proof uses the unit-equation theorem of Evertse, Schlickewei and Schmidt and Tijdeman's fixed-primes gap bound. [Unit equations](https://annals.math.princeton.edu/2002/155-3/p04) · [Tijdeman's paper](https://www.numdam.org/item/CM_1973__26_3_319_0/)

The last section gives the six values at $m=11$ through $16$ of Wei's sequence of largest primitive smooth sums, extracted from the authors' previously computed Table 1. [OEIS A376925](https://oeis.org/A376925) · [Original data](https://bmatschke.github.io/solving-classical-diophantine-equations/)

## Decimal rotations

A second manuscript proves an exact 33-integer list for A085135 under any of three conditions. The word has exactly two nonzero digits, some cyclic pair of consecutive nonzero digits has at most two zeros between them, or at least one quarter of its digits are nonzero. Any further nontrivial example has at least 19 digits and at least three nonzero digits. The complete sparse case remains open here. The paper also proves that every positive 7-smooth decimal integer has full period as a word. [Rotation manuscript (PDF)](smooth-rotations.pdf) · [LaTeX](smooth-rotations.tex) · [Earlier finiteness proof](../A085135/README.md) · [OEIS A085135](https://oeis.org/A085135)

## Using the catalogue

Python 3.9 or later is sufficient. Run these commands in this directory. Each line of query output gives the index and the exact value.

```sh
python3 gaps.py 7 31 1849 3737 14641
python3 gaps.py 5 --prefix 333333 > b391077.txt
python3 gaps.py 7 --prefix 47619 > b376924.txt
python3 verify.py
```

The lookup covers every positive index for which the product of the primes in $S$ and the **distinct** primes outside $S$ dividing the index is at most $10^7$. The compressed table stores the rough part, primitive gap, and upper endpoint after the dominance test proved in the paper. The standard audit checks all 380,952 prefix entries by direct enumeration from the global height bound, reads them back by individual lookup, and verifies the decimal list. [Catalogue](catalogue.tsv.gz) · [Lookup](gaps.py) · [Reproduction code](verify.py) · [Rotation enumeration](rotations.py)

For an audit from the original data, run `python3 verify.py --upstream`. It downloads two pinned files (about 100 MB total), checks their SHA-256 digests, verifies the radical and primitive-sum conditions, reconstructs the full catalogue, checks the ten Lean input lists, and extracts the A376925 maxima. Local copies can instead be specified with `--radical-file PATH --primes-file PATH`. Completeness of the two input enumerations is the published result of Rafael von Känel and Benjamin Matschke. Their data files specify Creative Commons BY-NC 3.0. The included numerical catalogue and lists derived from their data retain this attribution and license. [Authors' tables](https://bmatschke.github.io/solving-classical-diophantine-equations/) · [Pinned upstream revision](https://github.com/bmatschke/solving-classical-diophantine-equations/tree/97034f286c52b8e64f82bf00816a561aa01e26cd) · [CC BY-NC 3.0](https://creativecommons.org/licenses/by-nc/3.0/)

## Formal verification

Run `lake build` with Lean 4.19.0 and the pinned mathlib revision. The kernel checks the gcd reduction, the four infinite families, both maxima at 31, the two boundary values in each sequence, and the existence of earlier witnesses. The comparisons that exclude larger endpoints take the relevant published triple list's completeness as a hypothesis. The proof of an earlier witness at every smaller index is self-contained. For rotations the kernel checks elimination of the modulus and the denominator bound. The distribution theorem, the length bounds and the application of the external tables are justified in the manuscripts. [Gcd reduction](Gap.lean) · [Infinite families](Families.lean) · [Individual maxima and zeros](Milestones.lean) · [First-occurrence witnesses](Prefixes.lean) · [Rotation algebra](Rotation.lean) · [Build and audit output](verification.txt) · [File checksums](SHA256SUMS)
