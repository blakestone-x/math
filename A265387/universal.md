# Five-phase oscillation from arbitrary seeds

For either Gray-code Fibonacci recurrence, **every positive integer seed pair has mean growth 2**. From the sixth to seventh term onward, each step adds exactly one binary digit. From the seventh term onward, the terms of the first recurrence begin with `11` and those of the conjugate recurrence begin with `10`. The seed pair $(16,1)$ in the first recurrence shows both cutoffs are sharp. [Proof manuscript](universal.pdf) · [LaTeX source](universal.tex)

| Consecutive-term behavior | Result |
|---|---|
| Every positive pair for $a_{n+2}=G(a_n+a_{n+1})$ | The signs of $a_{n+1}-2a_n$ eventually repeat a cyclic shift of $+-+--$. |
| Every positive pair for $b_{n+2}=G(b_n)+G(b_{n+1})$ | The signs eventually repeat a cyclic shift of $+----$ or $++-+-$. Both patterns occur, already from $(2,1)$ and $(1,1)$ respectively. |
| Every seed in either recurrence | Five disjoint compact sets of ratios are visited by the five residue classes. The eventual ratio separation at any lag indivisible by five exceeds $0.00086$ for $a$ and $0.00031$ for $b$. |
| Original seed $(1,1)$ | Each sequence has at least **141** distinct accumulation points of consecutive ratios. Every progression modulo 70 fails to converge. The 140 progressions cannot all converge, and the limsup of the absolute lag-140 ratio difference exceeds $2^{-381}$. |

The universal growth proof uses six prefix states and is given in full on the first page. Lean 4.19 checks the [universal prefix theorem](UniversalGrowth.lean) and [both real limits for both recurrences](UniversalLimits.lean) for every positive seed pair. The universal oscillation proof reduces to 677 recurrent prefix pairs at 23-bit precision. For the original seeds, a separate certificate excludes near returns of normalized pairs at 184-bit precision. The precise number of accumulation points remains open. The oscillation and near-return results use the exact Python certificates.

Run the two exact Python verifiers from this directory. The second command performs the 53 precision steps in both Gray coordinates.

```sh
lake build
python3 universal_verify.py
python3 return_verify.py --cross-check
```

[Universal verifier](universal_verify.py) · [Lag-140 verifier](return_verify.py) · [Earlier 70-band paper](manuscript.pdf) · [Sykora's first sequence](https://oeis.org/A265385) · [Sykora's conjugate sequence](https://oeis.org/A265387)
