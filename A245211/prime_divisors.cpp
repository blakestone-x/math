#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

// Find a prime dividing H_e(x) in (lower, upper] for each supplied row.
// Every prime in this interval exceeds x and the canceled divisor D+1.
using u64 = std::uint64_t;
struct Query {
    u64 base, exponent, upper, witness;
};

u64 power_mod(u64 base, u64 exponent, u64 prime) {
    u64 result = 1;
    while (exponent) {
        if (exponent % 2) result = result * base % prime;
        base = base * base % prime;
        exponent /= 2;
    }
    return result;
}

int main() {
    u64 lower = 0, largest = 0;
    std::size_t size = 0;
    if (!(std::cin >> lower >> size)) return 1;
    std::vector<Query> queries(size);
    for (auto &q : queries) {
        if (!(std::cin >> q.base >> q.exponent >> q.upper)) return 1;
        if (q.base >= lower || q.upper >= (u64{1} << 31)) return 2;
        q.witness = 0;
        largest = std::max(largest, q.upper);
    }

    u64 root = static_cast<u64>(std::sqrt(largest));
    while ((root+1)*(root+1) <= largest) ++root;
    while (root*root > largest) --root;
    std::vector<u64> small;
    for (u64 n = 2; n <= root; ++n) {
        bool prime = true;
        for (u64 d : small) {
            if (d*d > n) break;
            if (n % d == 0) { prime = false; break; }
        }
        if (prime) small.push_back(n);
    }
    constexpr u64 width = 1u << 19;
    for (u64 start = lower+1; start <= largest; start += width) {
        const u64 stop = std::min(largest, start+width-1);
        std::vector<bool> prime(stop-start+1, true);
        for (u64 d : small) {
            if (d*d > stop) break;
            const u64 first = std::max(d*d, ((start+d-1)/d)*d);
            for (u64 n = first; n <= stop; n += d) prime[n-start] = false;
        }
        std::vector<u64> segment;
        for (u64 n = start; n <= stop; ++n)
            if (prime[n-start]) segment.push_back(n);
        for (auto &q : queries) {
            if (q.witness || q.upper < start) continue;
            const u64 slope = (q.exponent+1)*q.base-(q.exponent+2);
            for (u64 t : segment) {
                if (t > q.upper) break;
                const u64 v = power_mod(q.base, q.exponent+1, t);
                if ((v*(slope%t)+1)%t == 0) { q.witness=t; break; }
            }
        }
    }
    for (const auto &q : queries) std::cout << q.witness << '\n';
}
