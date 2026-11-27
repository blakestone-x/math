# A245211 verification

The conjecture asks whether 21 is the only positive integer equal to the sum of d times its number of divisors over all proper positive divisors d. The revised research note proves three results for unrestricted prime sizes and exponents.

- The only fixed point with at most two distinct prime factors is 21. Sections 3 and 4 give a hand proof, including all small exponent cases.
- No number of the form p^a q s with three distinct primes is a fixed point. Section 5 proves a ≤ 9 in a hypothetical solution, and the two independent searches below eliminate all surviving exponents.
- For every prescribed number of distinct prime factors, a finite algorithm enumerates every fixed point, allowing all prime exponents to vary. Section 6 proves an explicit recursive bound. This bound grows rapidly.

In the squarefree case the first count left by the combined results in the note is 203. The full uniqueness conjecture remains open.

## Quick checks

Run the following commands from this directory. Run Python normally so that assertions are active. The Python verification scripts use the standard library.

~~~sh
python3 three_primes.py
python3 three_primes_independent.py
python3 test_extension.py
~~~

The last command and the extension below also require g++ with C++17 support and the GMP C++ development library. The driver builds the executable in a temporary directory. All transcripts were produced with Python 3.12.14.

## Mixed three-prime case

For each sorted assignment of the exponents to x < y < z, `three_primes.py` calculates exact bounds on x and y and the single possible z from the rational residual in the divisor equation. Its four count columns give first-prime choices after the positive residual test, second-prime choices, ordered last candidates, and odd last candidates. It checks the polynomial identity before asking whether an integer root at z is prime. The 1,039 odd candidates for the four possible repeated exponents yield no equalities.

`three_primes_independent.py` uses monotone rational functions to bound the first two prime bases and bisection in the last integer base. Both implementations also recover six odd composite last bases in the squarefree control with three primes. Their results are in `results/three-prime.txt` and `results/three-prime-independent.txt`.

## Extended squarefree computation

~~~sh
python3 replay_extension.py 105
python3 replay_extension.py
~~~

The first command runs both halves of the exhaustive search at 105 prime factors. The full command runs all the counts in `extended-factors.json`. `results/extended-squarefree.txt` gives the count r, the two inclusive endpoints of the longest-gap interval, the first surviving gap (−1 for none), and the number of backward states expanded. Timing and memory depend on the machine.

`replay_extension.py` verifies the product of the supplied prime powers and recursively checks each of their primality certificates before starting the native search. `gap_cycle.cpp` independently checks the product and enumerates assignments of the prime factors of 2^r+1 to coefficient positions, allowing several factors at one position. It roots each cycle at a longest run of unit coefficients. The root has p+1 congruent to zero modulo each eligible primitive-root prime h with h ≤ L+2. All reported exclusions use necessary residue conditions, including the extra completion tables described in the note. A nonnegative survivor is reported as unresolved and causes the driver to fail.

`test_extension.py` compares the native search, separately at every possible longest gap, to direct enumeration and literal evaluation of the cycle formula through 25 prime factors. It also checks the primitive-root property of every auxiliary prime. All 170 comparisons agree, including four positive controls. The elementary modulo-3 proof in Section 2 covers every count 7·3^j, including 189. The odd prime-power and even-count theorems cover all other counts omitted below the stated boundary.

## Earlier squarefree and two-prime checks

~~~sh
python3 direct_check.py
python3 test_gap_sieve.py
python3 squarefree.py
python3 squarefree_forward.py
python3 test_two_primes.py
python3 two_primes.py 100
~~~

- `squarefree.py` verifies `factors.json` and checks 2 and every odd count through 101. It enumerates 3,167,295 orders of nonunit factors. Seven gap assignments reach the final small-divisor screen, and only the cycle 3, 7 survives.
- `direct_check.py` assigns the prime occurrences directly to positions and evaluates each cycle. It exhausts 22,543 assignments through 25 factors, including the positive control at two.
- `squarefree_forward.py` uses forward gap enumeration with a different pruning rule through 63 prime factors. It sends 26,224,057 gap assignments to the small-divisor test.
- `test_gap_sieve.py` validates backward gap screening against direct forward evaluation with reduced prime sets, including 337 positive controls.
- `two_primes.py` is the earlier bounded computation of every p^a q^b with p < q and b ≤ 100. The complete theorem in Section 4 also covers all higher exponents. `test_two_primes.py` compares its formulas to direct sums.

The [research note](../A245211-research.pdf) and its [LaTeX source](../A245211-research.tex) contain the algebraic proofs. Reference transcripts for the commands above are included in `results/`.

## References

1. [J. Krizek, OEIS A245211](https://oeis.org/A245211)
2. [Weighted Proper-Divisor Sum, earlier results and finite checks](https://github.com/umaia1234/agentic-conjectures/blob/78a56edb19eadb6a23f5f791273f016e0b3e0f50/problems/oeis-a245211/DETAILS.md)
3. [M. A. Sugui, Formal Verification of Parity Obstructions and Fixed-Point Exclusions for Proper-Divisor Moments](https://doi.org/10.5281/zenodo.24437886)
