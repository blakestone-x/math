#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>

using u64 = std::uint64_t;
struct Totals { u64 moment=1, divisors=1, sum=1; };

Totals multiplicative_totals(unsigned n, const std::vector<std::uint16_t>& least) {
    Totals result;
    while (n > 1) {
        unsigned p = least[n/2] ? least[n/2] : n;
        unsigned e=0;
        u64 power=1, h=1, sigma=1;
        do {
            n /= p;
            power *= p;
            ++e;
            h += (e+1)*power;
            sigma += power;
        } while (n%p == 0);
        result.moment *= h;
        result.divisors *= e+1;
        result.sum *= sigma;
    }
    return result;
}

int main() {
    constexpr unsigned limit=100'000'000;
    std::vector<std::uint16_t> least(limit/2+1);
    for (unsigned p=3; p*p<=limit; p+=2) if (!least[p/2]) {
        for (unsigned t=p*p; t<=limit; t+=2*p) if (!least[t/2]) least[t/2]=p;
    }
    unsigned found=0, tested=0;
    for (unsigned m=3; m<=limit; m+=2) {
        const auto f=multiplicative_totals(m,least);
        const u64 u=m*f.divisors, t=f.moment-u, b=u-f.sum;
        ++tested;
        bool equal=(t==b); // the a=0 test
        const u64 a=b/t;
        if (a>0 && a<63) {
            const u64 remainder=b%t;
            // Exact test of 2^(a+1) * remainder == b+t without overflow.
            const u64 v=b+t;
            const u64 power=u64{1} << (a+1);
            equal |= (v%power==0 && v/power==remainder);
        }
        if (equal) { std::cout << "odd-part equality: " << m << '\n'; ++found; }
    }
    std::cout << "Nontrivial odd parts checked through " << limit << ": " << tested
              << ". Equalities at any dyadic exponent: " << found << ".\n";
    return found != 0;
}
