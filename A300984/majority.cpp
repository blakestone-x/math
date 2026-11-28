// Count the distinct odd prime bases represented by A300984 through each
// decimal cutoff. The classification in Proof.lean reduces the search to
// n=2^i*p^j with i,j >= 2, p=1 mod 12 and 3(p+1) squarefree.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <vector>

using U = std::uint64_t;

static U isqrt(U x) {
    U r = static_cast<U>(std::sqrt(static_cast<long double>(x)));
    while (r + 1 <= x / (r + 1)) ++r;
    while (r && r > x / r) --r;
    return r;
}

static bool squarefree(U value, const std::vector<unsigned>& primes) {
    if (value == 0) return false;
    for (U p : primes) {
        if (p > value / p / p) break;
        if (value % p == 0) {
            value /= p;
            if (value % p == 0) return false;
        }
    }
    // After removing small factors once, the remaining integer has at most
    // two prime factors with multiplicity; it fails exactly at a square > 1.
    U r = isqrt(value);
    return value == 1 || r * r != value;
}

int main(int argc, char** argv) {
    int maxExponent = argc > 1 ? std::atoi(argv[1]) : 14;
    if (maxExponent < 7 || maxExponent > 16) return 2;
    std::vector<U> bounds(1, 1);
    for (int m = 1; m <= maxExponent; ++m) bounds.push_back(10 * bounds.back());
    const U bound = bounds.back();
    unsigned cap = static_cast<unsigned>(isqrt(bound / 4));
    std::vector<bool> prime(cap + 2, true), excluded(cap + 2, false);
    std::vector<unsigned> primes;
    prime[0] = prime[1] = false;
    for (unsigned q = 2; q <= cap; ++q) {
        if (!prime[q]) continue;
        primes.push_back(q);
        if (q <= cap / q)
            for (unsigned v = q * q; v <= cap; v += q) prime[v] = false;
        // Mark p+1 with a smaller prime q such that q+1 divides p+1.
        for (unsigned v = 2 * (q + 1); v <= cap + 1; v += q + 1)
            excluded[v] = true;
    }
    std::vector<U> total(maxExponent + 1), good(maxExponent + 1);
    for (U p : primes) {
        if (p % 12 != 1 || !squarefree(3 * (p + 1), primes)) continue;
        U first = bound + 1, power = p*p, geometric = 1 + p + power;
        while (power <= bound / 4 && 4*power < first) {
            for (U two = 4; two <= bound / power && two*power < first; two *= 2) {
                U T = (2*two - 1) * geometric - 3*(p+1);
                if (squarefree(T, primes)) {
                    first = two * power;
                    break;
                }
            }
            if (power > (bound/4) / p) break;
            power *= p;
            geometric += power;
        }
        for (int m = 7; m <= maxExponent; ++m) {
            if (first > bounds[m]) continue;
            ++total[m];
            if (!excluded[p + 1]) ++good[m];
        }
    }
    std::cout << "m,represented,A082539,others\n";
    for (int m = 7; m <= maxExponent; ++m)
        std::cout << m << ',' << total[m] << ',' << good[m] << ',' << total[m]-good[m] << '\n';
}
