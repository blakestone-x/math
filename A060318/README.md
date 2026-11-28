# Smallest prime factors of odd Catalan numbers (A060318)

For exponents n ≥ 2, OEIS conjectures that the smallest prime factor of the Catalan number with index 2ⁿ−1 is 3, with exceptions at 2, 5 and 8. Their least factors are 5, 7 and 7. The full conjecture remains open.

## Lean theorems

- `minFac_three_iff` detects the factor 3 exactly when the base-three expansion of 2ⁿ−1 contains a 2. The proof uses Lucas's theorem and proves that each of these Catalan numbers is odd.
- `classification_iff` identifies the full conjecture with two digit conditions. For even n > 8, the expansion of 2ⁿ must contain a 2. For odd n > 8, it must contain a 2 above the units digit. The named small cases are computed exactly.
- `exceptional_count` bounds the number of exceptional exponents below 2·3ᵏ by 2ᵏ⁺¹, including 0 and 1. Powers of 2 are distinct modulo 3ᵏ⁺¹ over the specified range, and just 2ᵏ⁺¹ residue classes have all of those ternary digits in {0,1}. `exceptional_density_zero` proves the limiting proportion is zero over all initial intervals.
- `Sieve.no_three` proves that 2ⁿ = 1 + 3ᵃ + 3ᵇ + 3ᶜ has no solutions for n > 8, even when a, b and c may repeat. Every modular filtering step covers every lift of every surviving residue class. The final list is empty by Lean kernel evaluation. `Sieve.five_or_more` deduces that any further exception requires an odd number of at least five distinct powers of 3 in 2ⁿ−1.

Run `lake exe cache get` and `lake build` in this directory using the pinned Lean toolchain. The theorems use only the standard axioms reported by Lean. The independent finite computation, `python3 check_range.py`, uses exact modular arithmetic and verifies the classification for every integer 2 ≤ n ≤ 1,000,000,000.

## Context

The even-exponent condition is the nontrivial part of Erdős's ternary-digits conjecture. Dimitrov and Howe classified powers of 2 that are sums of at most 25 **distinct** powers of 3. In our three-power equation the separate constant 1 can coincide with a summand; our certificate also allows repeated exponents elsewhere.

[OEIS A060318](https://oeis.org/A060318) · [Dimitrov and Howe](https://arxiv.org/abs/2105.06440) · [Left to Solve reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/20433)
