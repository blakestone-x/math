# The three-prime classification

**Among positive integers with at most three distinct prime factors, 21 is the only fixed point of Krizek’s weighted proper-divisor sum.** Its proper divisors contribute $1+6+14=21$. The proof excludes all triples of distinct prime bases with arbitrary positive exponents. The original conjecture remains open for four or more distinct primes. [Manuscript](three-primes.pdf) · [Editable LaTeX](three-primes.tex) · [Krizek’s statement](https://oeis.org/A245211)

For any four-prime fixed point at least one exponent would have to be at most 24. No four-prime fixed point has all four exponents equal. For an arbitrary number $r$ of distinct prime factors the paper bounds the integer by a power of its radical, the product of those primes.

The previous paper bounded the three exponents. The new argument truncates each possible subset of the local divisor moments. An integer lower bound for the resulting error forces inequalities among the three base sizes. If every exponent is at least ten, the inequalities give a contradiction by hand. The four remaining minimum exponents are 4, 6, 8 and 9. Exact interval bounds reduce these to 6,053 least-prime cases. [Preceding exponent bounds](simple-prime.md)

The first completion scans the admissible middle primes and checks each possible largest prime by exact multiplication. The independent completion finds a divisor of the first local moment, or recovers a power of the largest prime, and checks the missing base by monotone bisection. Both use integer arithmetic. [Exponent sieve](three_prime_profiles.py) · [Interval proof and complete prime enumeration](three_prime_verify.cpp) · [Independent completion](three_prime_crosscheck.py) · [Recorded counts](three-prime-verification.txt)

Run from this directory with Python 3.8 or later, a C++20 compiler supporting 128-bit unsigned integers, and the GMP C++ library.

```sh
python3 -B three_prime_profiles.py > /tmp/krizek-profiles.txt
c++ -O3 -std=c++20 three_prime_verify.cpp -lgmpxx -lgmp -o /tmp/krizek-three
/tmp/krizek-three /tmp/krizek-intervals.txt < /tmp/krizek-profiles.txt
python3 -B three_prime_crosscheck.py /tmp/krizek-intervals.txt
```

The verifier writes 181 surviving intervals for the smallest base. Their SHA-256 digest is `da031fdc4b89d183d6ede477ced9bce2eb1d234b7f874d1f7e2c420ba3e0d6bf`. The largest middle-prime sieve endpoint is 48,554,105. No integer equality survived either completion.

An [independent full audit](three-prime-independent.md) also reconstructs the exponent sieve and the logarithmic exclusion using different interval partitions, precision and arithmetic, then completes its remaining cases separately.
