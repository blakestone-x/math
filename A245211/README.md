# Partial results on fixed points of OEIS A245211

**Blake Stone · Developed with OpenAI Astra 6.2**

Jaroslav Krizek asked whether $21$ is the only positive integer $n$ equal to the sum of $d\,\tau(d)$ over its proper positive divisors, where $\tau(d)$ is the number of positive divisors of $d$. The proper divisors of $21$ give $1+6+14=21$. The unrestricted conjecture remains open. [OEIS A245211](https://oeis.org/A245211)

**Theorem.** Among all positive integers with at most two distinct prime factors, $21$ is the only fixed point. This holds for arbitrary prime bases and exponents.

Sections 3 and 4 give the proof by hand. For $n=p^a q^b$ with $p<q$, the fixed-point equation forces $b\le a<3b$. If $b\ge4$, clearing the prime-power moment denominators produces a positive integer smaller than $5/p<1$. Congruences finish the cases $b=1,2,3$. [Research note, pages 3–4](A245211-research.pdf#page=3)

| Additional result | Location |
| --- | --- |
| No fixed point has the form $p^a q s$ for three distinct primes and any $a\ge1$. Two independent programs check the four remaining repeated exponents. | [Section 5](A245211-research.pdf#page=5) |
| A squarefree fixed point other than $21$ requires at least 203 distinct primes and at least 12,406 decimal digits. | [Sections 1–2](A245211-research.pdf#page=1) and [Section 7](A245211-research.pdf#page=7) |
| For every prescribed number of distinct prime factors, all fixed points with that number of factors can be found by a finite algorithm. | [Section 6](A245211-research.pdf#page=6) |

The verification directory contains the Python and C++ programs, factorizations with primality certificates, and run transcripts for the computer-assisted results. [Full PDF](A245211-research.pdf) · [LaTeX source](A245211-research.tex) · [Reproduce the computations](verification/README.md)

Earlier work established prime-factor and parity restrictions and reported finite searches, including a search with both two-prime exponents at most 200. The note credits those results where used. [Earlier A245211 results](https://github.com/umaia1234/agentic-conjectures/blob/78a56edb19eadb6a23f5f791273f016e0b3e0f50/problems/oeis-a245211/DETAILS.md) · [Mar Allen Sugui’s preprint](https://doi.org/10.5281/zenodo.24437886)
