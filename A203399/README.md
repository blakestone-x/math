# Which rows of the binary bracelet table obey the divisor rule?

Geoffrey Critzer’s table counts binary bracelets by how many distinct words they produce under rotation and reversal. Petros Hadjicostas proposed a formula in 2019 and later found counterexamples at lengths 18 and 21. This note gives the corrected formula for every entry and determines exactly where his original formula succeeds. Independent mathematical review is pending. [Manuscript (PDF)](bracelet-orbits.pdf) · [LaTeX](bracelet-orbits.tex) · [Original prediction and counterexamples](https://oeis.org/A203399)

**The original formula holds on the entire row exactly at the powers of two, at $p,2p,4p$ for odd primes $p$, and at $9,15,25$.** Only about $7x/(4\log x)$ lengths up to $x$ qualify. The fraction of rows containing a counterexample tends to one.

A word with least rotational period $d$ produces $d$ rotations. Reversing it gives those same rotations if the primitive necklace has a reflection symmetry. Otherwise it gives a second set of $d$ rotations. If $R(d)$ counts the symmetric primitive necklaces and $C(d)$ counts the pairs of reversed asymmetric primitive necklaces, then

$$
T(n,k)=\sum_{\substack{d\mid n\\ d=k}}R(d)+\sum_{\substack{d\mid n\\2d=k}}C(d).
$$

The summands use the established primitive-bracelet counts. With two colors, an asymmetric primitive bracelet exists at every length $d\ge6$. Put three black beads on the circle with successive white gaps of lengths $0,1,d-4$. A row has a positive entry at some $k\le n$ that does not divide $n$ exactly when $n$ has an odd divisor $t\ge3$ and $n/t\ge6$. The column is then $k=2n/t$. [Primitive symmetric counts](https://oeis.org/A056493) · [Primitive asymmetric counts](https://oeis.org/A032239) · [Hadjicostas on co-periods](https://doi.org/10.54550/ECA2023V3S3R23)

| Length | Orbit size | Original prediction | Correct count |
| ---: | ---: | ---: | ---: |
| 18 | 12 | 0 | 1 |
| 18 | 18 | 743 | 742 |
| 21 | 14 | 0 | 2 |
| 21 | 21 | 2032 | 2030 |

The paper also gives the formula for any number of colors. With three or more colors, the first asymmetric primitive length is three.

Run `python3 verify.py` to enumerate all binary words through length 21 and all ternary words through length 9, and to compare both rules at every length through 1,000. Adding `--oeis-repo /path/to/oeisdata` checks all 110 terms in the OEIS entry. [Verification code](verify.py)
