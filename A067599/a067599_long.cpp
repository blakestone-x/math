// Search the terminal-exponent-one family n=Kq for very long decimal lengths.
// g++ -std=c++17 -O3 a067599_long.cpp -lgmpxx -lgmp -o a067599_long
#include <algorithm>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <tuple>
#include <vector>

using Integer = std::uint64_t;
constexpr int upper_prefix = 30000000;
constexpr int upper_digits = 25000;

Integer decimal_place(Integer n) {
    Integer result = 10;
    while (result <= n) result *= 10;
    return result;
}

int main() {
    std::vector<int> least_factor(upper_prefix + 1);
    for (int i = 2; i <= upper_prefix; ++i) {
        if (least_factor[i]) continue;
        least_factor[i] = i;
        for (Integer j = Integer(i) * i; j <= upper_prefix; j += i)
            if (!least_factor[j]) least_factor[j] = i;
    }
    // For E(Kq)=Kq the product ends in 1.
    std::vector<std::tuple<int, int, Integer>> hits;
    int candidate_prefixes = 0;
    for (int k = 11; k <= upper_prefix; k += 2) {
        if (k % 5 == 0) continue;
        Integer code = 0;
        int remaining = k;
        while (remaining > 1 && code <= Integer(k / 10)) {
            int p = least_factor[remaining], e = 0;
            do {
                remaining /= p;
                ++e;
            } while (remaining % p == 0);
            code = (code * decimal_place(p) + p) * decimal_place(e) + e;
        }
        const Integer modulus = k - 10;
        if (remaining > 1 || 10 * code >= modulus || 100 * code < modulus) continue;
        if (modulus % 3 == 0 && (code + 1) % 3 != 0) continue;
        if (modulus % 9 == 0 && (code + 1) % 9 != 0) continue;
        if (modulus % 11 == 0 && code % 11 != 1 && code % 11 != 10) continue;
        ++candidate_prefixes;
        Integer residue = code * 10 % modulus;
        for (int d = 1; d <= upper_digits; ++d) {
            residue = residue * 10 % modulus;
            if (residue == modulus - 1) hits.emplace_back(d, k, code);
        }
    }
    std::sort(hits.begin(), hits.end());
    std::cout << "prefixes " << candidate_prefixes << ", integral candidates "
              << hits.size() << std::endl;
    mpz_class small_primes = 1;
    for (int i = 2; i <= 50000; ++i)
        if (least_factor[i] == i) small_primes *= i;
    int small_factors = 0, composite_tests = 0, possible_primes = 0;
    for (const auto& [d, k, code] : hits) {
        mpz_class q, common;
        mpz_ui_pow_ui(q.get_mpz_t(), 10, d + 1);
        q = q * code + 1;
        if (!mpz_divisible_ui_p(q.get_mpz_t(), k - 10)) return 2;
        q /= k - 10;
        mpz_gcd(common.get_mpz_t(), q.get_mpz_t(), small_primes.get_mpz_t());
        if (common > 1 && common < q) {
            ++small_factors;
        } else if (mpz_probab_prime_p(q.get_mpz_t(), 15) == 0) {
            ++composite_tests;
        } else {
            ++possible_primes;
            std::cout << "Primality certificate needed for K=" << k << " and d=" << d << std::endl;
        }
    }
    std::cout << "small factors " << small_factors << ", other composites " << composite_tests
              << ", possible primes " << possible_primes << '\n';
}
