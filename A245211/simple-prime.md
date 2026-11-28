# Three-prime fixed points must have every exponent at least four

For the weighted proper-divisor sum in [OEIS A245211](https://oeis.org/A245211), no fixed point with exactly three distinct prime factors can have an exponent one, two or three. If the ordered exponents are $a\ge b\ge c$, a possible three-prime counterexample must satisfy $4\le c\le25$, $b\le10c+7$, and $a\le(3c+4)b+3c$. The [preceding manuscript](A245211-research.pdf) excluded the case with two exponents equal to one.

[Proof manuscript](simple-prime.pdf) · [Editable LaTeX](simple-prime.tex) · [Recorded verification](simple_prime_verification.txt)

For a putative fixed point of the form $p^a q^b r$, with $a\ge b\ge1$, the proof gives $b\le16$ and $a\le7b+3$. An exact computation excludes all the remaining exponent pairs. The only surviving integer equality in this enumeration has ordered bases $7,15,31$, with composite middle base. When $c=2$, more precise bounds give $b\le25$ and $a\le10b+6$. A modular sieve leaves only two profiles, and neither satisfies the equation. An exponent three is impossible by parity.

A separate result applies to any number of prime factors. For every odd prime $\ell$, no exponent can be $-1$ modulo $\ell(\ell-1)$. In particular no exponent can be $5$ modulo $6$.

## Reproduction

From this directory run the following commands with a C++17 compiler and Python 3.10 or later. The programs use their standard libraries.

```sh
c++ -O3 -std=c++17 prime_divisors.cpp -o /tmp/a245211-simple-prime
python3 -B verify_simple_prime.py /tmp/a245211-simple-prime --cross-check
python3 -B verify_low_powers.py
```

The [Python verifier](verify_simple_prime.py) enumerates exponent patterns, prime bases, and exact candidate completions. The [C++ helper](prime_divisors.cpp) exhausts 42 extended prime-divisor intervals with integer modular exponentiation. The [independent checks](cross_check_simple_prime.py) validate every nonempty interval witness and exhaust the empty intervals with a different sieve and literal divisibility. They find the missing base again by monotone bisection for every completion.

The [exponent-two verifier](verify_low_powers.py) directly enumerates the two smaller prime bases through their proved bounds, then checks the exact last candidate in 47,103 full integral products. [Recorded exponent-two verification](low_powers_verification.txt)

For the next open case with smallest exponent four, `python3 -B verify_low_powers.py --fourth-power` applies the same 22 congruence tests to all 17,402 exponent profiles allowed by the theorem. There are 502 surviving profiles before prime-base enumeration. The existence of any three-prime fixed point is still open.
