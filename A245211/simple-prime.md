# Three-prime fixed points must be powerful

For the weighted proper-divisor sum in [OEIS A245211](https://oeis.org/A245211), no fixed point with exactly three distinct prime factors has a prime factor of exponent one. In a possible three-prime counterexample every prime dividing the number must divide it at least twice. The [preceding manuscript](A245211-research.pdf) excluded the case with two exponents equal to one.

[Proof manuscript](simple-prime.pdf) · [Editable LaTeX](simple-prime.tex) · [Recorded verification](simple_prime_verification.txt)

For a putative fixed point of the form $p^a q^b r$, with $a\ge b\ge1$, the proof gives $b\le16$ and $a\le7b+3$. An exact computation excludes all the remaining exponent pairs. The only surviving integer equality in the enumeration has ordered bases $7,15,31$, with composite middle base.

A separate result applies to any number of prime factors. For every odd prime $\ell$, no exponent can be $-1$ modulo $\ell(\ell-1)$. In particular no exponent can be $5$ modulo $6$.

## Reproduction

From this directory run the following commands with a C++17 compiler and Python 3.10 or later. The programs use their standard libraries.

```sh
c++ -O3 -std=c++17 prime_divisors.cpp -o /tmp/a245211-simple-prime
python3 -B verify_simple_prime.py /tmp/a245211-simple-prime --cross-check
```

The [Python verifier](verify_simple_prime.py) enumerates exponent patterns, prime bases, and exact candidate completions. The [C++ helper](prime_divisors.cpp) exhausts 42 extended prime-divisor intervals with integer modular exponentiation. The [independent checks](cross_check_simple_prime.py) validate every nonempty interval witness and exhaust the empty intervals with a different sieve and literal divisibility. They find the missing base again by monotone bisection for every completion.
