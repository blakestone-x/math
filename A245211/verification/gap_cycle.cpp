// Search for a necessary residue cycle, starting at a longest gap of unit coefficients.
// Build with g++ -std=c++17 -O2 gap_cycle.cpp -lgmpxx -lgmp -o gap_cycle
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <gmpxx.h>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <unordered_set>
#include <vector>

using Big = mpz_class;
using U64 = std::uint64_t;
using Mask = unsigned;

struct State {
    Mask remaining;
    int slots;
    U64 residue;
    bool operator==(const State &other) const {
        return remaining == other.remaining && slots == other.slots &&
               residue == other.residue;
    }
};
struct Hash {
    std::size_t operator()(const State &s) const {
        return std::hash<U64>()(s.residue * 1000003ull + U64(s.remaining) * 2003 + s.slots);
    }
};

struct CompletionTable {
    unsigned modulus;
    int threshold;
    std::vector<unsigned char> possible;
    bool contains(Mask mask, U64 value) const {
        return possible[std::size_t(mask) * modulus + value % modulus] != 0;
    }
};

class Search {
    int r_, longest_ = 0;
    const std::vector<Big> atoms_;
    Mask full_;
    std::vector<std::vector<Mask>> divisors_;
    std::vector<int> active_;
    std::vector<U64> coefficient_;
    std::unordered_set<State, Hash> failed_;
    U64 modulus_ = 1;
    std::vector<CompletionTable> tables_;
    std::vector<const CompletionTable *> active_tables_;
    // table[mask,y] allows any number of unit edges, in any positions.
    // It is a necessary condition on every exact completion of a partial cycle.
    void add_table(unsigned m, int threshold) {
        CompletionTable t{m, threshold,
                          std::vector<unsigned char>((std::size_t(full_) + 1) * m)};
        std::vector<unsigned> coefficients(full_ + 1, 1), half(m);
        std::vector<unsigned char> valid(m);
        for (unsigned y = 0; y < m; ++y) {
            half[y] = (y + (y % 2) * m) / 2;
            valid[y] = std::gcd((y + m - 1) % m, m) == 1;
        }
        for (Mask k = 1; k <= full_; ++k) {
            unsigned j = __builtin_ctz(k);
            coefficients[k] =
                coefficients[k & (k - 1)] * mpz_fdiv_ui(atoms_[j].get_mpz_t(), m) % m;
        }
        t.possible[0] = 1;
        std::vector<unsigned> queue;
        for (Mask mask = 1; mask <= full_; ++mask) {
            auto row = t.possible.begin() + std::size_t(mask) * m;
            queue.clear();
            for (unsigned y = 0; y < m; ++y) {
                if (!valid[y])
                    continue;
                for (Mask take : divisors_[mask]) {
                    unsigned z = half[(coefficients[take] * ((y + m - 1) % m) + 1) % m];
                    if (t.possible[std::size_t(mask ^ take) * m + z]) {
                        row[y] = 1;
                        queue.push_back(y);
                        break;
                    }
                }
            }
            // Prepending a backward unit step changes the start from z to 2z.
            for (std::size_t i = 0; i < queue.size(); ++i) {
                unsigned y = 2 * queue[i] % m;
                if (valid[y] && !row[y]) {
                    row[y] = 1;
                    queue.push_back(y);
                }
            }
        }
        tables_.push_back(std::move(t));
    }
    static int count(Mask bits) { return __builtin_popcount(bits); }
    U64 multiply(U64 a, U64 b) const {
        if (modulus_ <= 0xffffffffull)
            return a * b % modulus_;
        return (static_cast<__uint128_t>(a) * b) % modulus_;
    }
    U64 halve(U64 y) const { return (y + (y % 2) * modulus_) / 2; }
    bool allowed(U64 y) const {
        for (int prime : active_)
            if (y % prime == 1)
                return false;
        return true;
    }
    bool walk(Mask rem, int slots, U64 y) {
        if (slots < 1 || slots > count(rem) * (longest_ + 1) - longest_)
            return false;
        for (const auto *t : active_tables_)
            if (!t->contains(rem, y))
                return false;
        State st{rem, slots, y};
        if (failed_.find(st) != failed_.end())
            return false;
        ++visited;
        for (Mask take : divisors_[rem]) {
            Mask rest = rem ^ take;
            if ((rest == 0) != (slots == 1))
                continue;
            U64 z = halve((multiply(coefficient_[take], (y + modulus_ - 1) % modulus_) + 1) %
                          modulus_);
            if (!rest) {
                if (z == 0)
                    return true;
                continue;
            }
            int lo = std::max(0, slots - 1 - (count(rest) * (longest_ + 1) - longest_));
            int hi = std::min(longest_, slots - 2);
            for (int g = 0; g <= hi && allowed(z); ++g, z = halve(z)) {
                if (g >= lo && walk(rest, slots - 1 - g, z))
                    return true;
            }
        }
        failed_.insert(st);
        return false;
    }

  public:
    U64 visited = 0;
    Search(int r, std::vector<Big> atoms) : r_(r), atoms_(std::move(atoms)) {
        if (atoms_.empty() || atoms_.size() > 18)
            throw std::invalid_argument("1 to 18 prime factors required");
        Big product = 1;
        for (const auto &p : atoms_)
            product *= p;
        if (product != (Big(1) << r) + 1)
            throw std::invalid_argument("factorization has the wrong product");
        full_ = (Mask(1) << atoms_.size()) - 1;
        divisors_.resize(full_ + 1);
        coefficient_.resize(full_ + 1);
        for (Mask rem = 1; rem <= full_; ++rem) {
            for (Mask take = rem; take; take = (take - 1) & rem) {
                // Interchangeable copies of the same prime give identical moves.
                bool canonical = true;
                for (unsigned i = 1; i < atoms_.size(); ++i) {
                    if (atoms_[i] == atoms_[i - 1] && (take & (1u << i)) &&
                        (rem & (1u << (i - 1))) && !(take & (1u << (i - 1)))) {
                        canonical = false;
                        break;
                    }
                }
                if (canonical)
                    divisors_[rem].push_back(take);
            }
        }
    }
    int run(int lower = 0, int upper = 1000000) {
        for (int p : {3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83})
            if (p < (Big(1) << r_) - 1)
                add_table(p, p - 2);
        for (auto pair : {std::pair<unsigned, int>{15, 5},
                          {165, 11},
                          {195, 13},
                          {143, 13},
                          {209, 19},
                          {319, 29},
                          {407, 37}}) {
            if (pair.second < (Big(1) << r_) - 1)
                add_table(pair.first, pair.second - 2);
        }
        int k = atoms_.size();
        for (longest_ = std::max((r_ - 1) / k, lower); longest_ < r_ && longest_ <= upper;
             ++longest_) {
            active_.clear();
            modulus_ = 1;
            for (int prime : {3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83}) {
                if (prime - 2 <= longest_ && prime < (Big(1) << r_) - 1) {
                    active_.push_back(prime);
                    modulus_ *= prime;
                }
            }
            active_tables_.clear();
            for (const auto &tab : tables_)
                if (tab.threshold <= longest_) {
                    if (!tab.contains(full_, 0))
                        return -1;
                    active_tables_.push_back(&tab);
                }
            coefficient_[0] = 1 % modulus_;
            for (Mask mask = 1; mask <= full_; ++mask) {
                int i = __builtin_ctz(mask);
                U64 v = mpz_fdiv_ui(atoms_[i].get_mpz_t(), modulus_);
                coefficient_[mask] = multiply(coefficient_[mask & (mask - 1)], v);
            }
            failed_.clear();
            if (walk(full_, r_ - longest_, 0))
                return longest_;
        }
        return -1;
    }
};

int main(int argc, char **argv) {
    if (argc < 3)
        return 2;
    int r = std::stoi(argv[1]);
    std::vector<Big> factors;
    for (int i = 2; i < argc; ++i)
        factors.emplace_back(argv[i]);
    std::sort(factors.begin(), factors.end());
    Search search(r, factors);
    const char *lo = std::getenv("A245_MIN_GAP");
    const char *hi = std::getenv("A245_MAX_GAP");
    int gap = search.run(lo ? std::stoi(lo) : 0, hi ? std::stoi(hi) : r - 1);
    std::cout << r << " " << gap << " " << search.visited << "\n";
}
