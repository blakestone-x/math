// Exact seed cases for the fixed-point induction for OEIS A218468.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

int main() {
    constexpr unsigned limit = 20000000;
    std::vector<std::uint64_t> taken(limit / 64 + 1);
    auto used = [&](unsigned n) { return n / 64 < taken.size() &&
        ((taken[n / 64] >> (n % 64)) & 1U); };
    auto mark = [&](unsigned n) {
        if (n / 64 >= taken.size()) taken.resize(n / 64 + 1);
        taken[n / 64] |= std::uint64_t{1} << (n % 64);
    };
    std::array<unsigned,10> next = {0,1,2,3,4,5,6,7,8,9};
    unsigned current=1, largest=1, boundary=2;
    mark(current);
    std::cout << "index,last,largest\n";
    for (unsigned i=2; i<=limit; ++i) {
        unsigned best=0;
        for (unsigned v=current; v; v/=10) {
            const unsigned d=v%10;
            if (d==0) continue;
            while (used(next[d])) next[d]+=d;
            if (best==0 || next[d]<best) best=next[d];
        }
        if (!best || used(best)) throw std::logic_error("invalid greedy term");
        current=best;
        mark(current);
        largest=std::max(largest,current);
        if (i==boundary) {
            std::cout << i << ',' << current << ',' << largest << '\n';
            if (current!=i || largest!=i) throw std::logic_error("prefix incomplete");
            boundary*=10;
        }
    }
}
