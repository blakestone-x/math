// Exhaustive search for E(n) = n, where E writes each prime and exponent in order.
// Compile with g++ -std=c++17 -O3 a067599.cpp -o a067599.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Integer = std::uint64_t;
using Wide = __uint128_t;

struct Search {
    Integer limit, offset, prefixes = 0;
    std::vector<Integer> primes, powers{1}, matches;

    Search(Integer upper, Integer difference) : limit(upper), offset(difference) {
        if (limit < 2 || limit > 1000000000000000ULL || offset > limit)
            throw std::invalid_argument("require 2 <= limit <= 10^15 and offset <= limit");
        while (powers.back() <= limit) powers.push_back(10 * powers.back());
        powers.push_back(10 * powers.back());
        // Exact integer-square-root envelope, including all possible trial divisors.
        auto root = static_cast<Integer>(std::sqrt(static_cast<long double>(limit)));
        while ((root + 1) * (root + 1) <= limit) ++root;
        while (root * root > limit) --root;
        std::vector<bool> sieve(root + 1, true);
        for (Integer i = 2; i <= root; ++i) {
            if (!sieve[i]) continue;
            primes.push_back(i);
            for (Integer j = i * i; j <= root; j += i) sieve[j] = false;
        }
    }

    Integer decimal_place(Integer x) const {
        return *std::upper_bound(powers.begin(), powers.end(), x);
    }

    bool is_prime(Integer n) const {
        if (n < 2) return false;
        for (auto prime : primes) {
            if (prime * prime > n) break;
            if (n % prime == 0) return false;
        }
        return true;
    }

    void search_single_final_prime(Integer product, Integer code, Integer min_prime) {
        // E(n) + offset = n gives (product - 10) * q = code * 10^(d+1) + 1 + offset.
        if (product <= 10) return;
        const Integer coefficient = product - 10;
        if (Wide(10) * code >= coefficient ||
            Wide(100) * code + 1 + offset < coefficient) return;
        for (std::size_t d = 1; d + 1 < powers.size() && powers[d - 1] <= limit / product; ++d) {
            const Wide numerator = Wide(code) * powers[d + 1] + 1 + offset;
            if (numerator % coefficient != 0) continue;
            const Wide q = numerator / coefficient;
            if (q < min_prime || q < powers[d - 1] || q >= powers[d] || q > limit / product)
                continue;
            if (is_prime(static_cast<Integer>(q)))
                matches.push_back(product * static_cast<Integer>(q));
        }
    }

    void visit(Integer product, Integer code, std::size_t next_index) {
        ++prefixes;
        const Integer min_prime = next_index == 0 ? 2 : primes[next_index - 1] + 1;
        search_single_final_prime(product, code, min_prime);
        for (std::size_t i = next_index; i < primes.size(); ++i) {
            const Integer p = primes[i];
            if (p * p > limit / product) break;
            const Wide with_prime = Wide(code) * decimal_place(p) + p;
            if (with_prime * 10 + 1 > limit) break;
            Integer new_product = product * p;
            for (Integer exponent = 1; ; ++exponent) {
                const Wide new_code = with_prime * decimal_place(exponent) + exponent;
                if (exponent >= 2 && new_code + offset == new_product)
                    matches.push_back(new_product);
                // An extension supplies a larger prime and at least two decimal digits.
                if (new_product <= limit / p && new_code * 100 <= limit)
                    visit(new_product, static_cast<Integer>(new_code), i + 1);
                if (new_product > limit / p) break;
                new_product *= p;
            }
        }
    }

    void run() {
        visit(1, 0, 0);
        std::sort(matches.begin(), matches.end());
    }
};

int main(int argc, char** argv) {
    const Integer limit = argc > 1 ? std::stoull(argv[1]) : 1000000000000000ULL;
    const Integer offset = argc > 2 ? std::stoull(argv[2]) : 0;
    Search search(limit, offset);
    search.run();
    for (const auto n : search.matches) std::cout << "match " << n << '\n';
    std::cout << "limit " << limit << ", offset " << offset
              << ", matches " << search.matches.size() << ", prefixes " << search.prefixes << '\n';
}
