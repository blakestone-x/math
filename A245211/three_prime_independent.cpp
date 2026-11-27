// Independent interval proof for the three-prime divisor-moment classification.
// Read oriented exponent triples from standard input and write the surviving
// (i,j,k,x) rows to the supplied path.
#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <queue>
#include <stdexcept>
#include <utility>

using UInt = std::uint64_t;
using Wide = __uint128_t;
using Tick = std::int64_t;
using Triple = std::array<int, 3>;
using Bounds = std::array<Tick, 3>;

constexpr int scale = 64;
std::array<int, 8193> exact_logs;

int head_shift(Wide value) {
    if (value == 0) throw std::runtime_error("logarithm of zero");
    UInt high = static_cast<UInt>(value >> 64);
    int length = high ? 64 + std::bit_width(high) : std::bit_width(static_cast<UInt>(value));
    return std::max(0, length - 13);
}

// Every tick is 1/64 of a binary logarithm. Calculate an interval with
// rigorous integer arithmetic by taking the top thirteen bits of the input.
Tick log_lo(Wide value) {
    int shift = head_shift(value);
    return scale * shift + exact_logs[static_cast<unsigned>(value >> shift)];
}

Tick log_hi(Wide value) {
    int shift = head_shift(value);
    unsigned head = static_cast<unsigned>(value >> shift);
    return scale * shift + exact_logs[head + (shift != 0)] + 1;
}

Tick floor_quotient(Tick numerator, int denominator) {
    return numerator >= 0 ? numerator / denominator : -((-numerator + denominator - 1) / denominator);
}

Tick ceil_quotient(Tick numerator, int denominator) {
    return -floor_quotient(-numerator, denominator);
}

// coeff[w] * log(p[w]) <= constant + sum_{s!=w} coeff[s] * log(p[s]).
struct Inequality {
    int witness;
    Triple coeff;
    Tick constant;
};

using System = std::array<Inequality, 9>;

bool consistent(const System& system, Bounds low, Bounds high) {
    for (int pass = 0; pass < 12; ++pass) {
        auto old_low = low;
        auto old_high = high;
        for (int t = 0; t < 2; ++t) {
            low[t + 1] = std::max(low[t + 1], low[t]);
            high[1 - t] = std::min(high[1 - t], high[2 - t]);
        }
        for (const auto& row : system) {
            int w = row.witness;
            int a = (w + 1) % 3, b = (w + 2) % 3;
            const auto& c = row.coeff;
            Tick rhs = row.constant + c[a] * high[a] + c[b] * high[b];
            if (c[w] * low[w] > rhs) return false;
            high[w] = std::min(high[w], ceil_quotient(rhs, c[w]));
            if (c[a]) {
                Tick numerator = c[w] * low[w] - row.constant - c[b] * high[b];
                low[a] = std::max(low[a], floor_quotient(numerator, c[a]));
            }
            if (c[b]) {
                Tick numerator = c[w] * low[w] - row.constant - c[a] * high[a];
                low[b] = std::max(low[b], floor_quotient(numerator, c[b]));
            }
        }
        for (int h = 0; h < 3; ++h) if (low[h] > high[h]) return false;
        if (low == old_low && high == old_high) break;
    }
    return true;
}

class Profile {
public:
    Triple e;
    UInt K, D, P;

    explicit Profile(Triple exponents) : e(exponents) {
        K = (e[1] + 1) * (e[2] + 1);
        D = (e[0] + 1) * K;
        P = D + 1;
        Triple order{0, 1, 2};
        int system_index = 0;
        do {
            auto& system = systems[system_index++];
            int index = 0;
            for (unsigned mask : {7, 3, 5, 6, 1, 2, 4}) {
                int witness = -1;
                for (int t : order) {
                    if (mask & (1u << t)) { witness = t; break; }
                }
                Triple coeff{};
                for (int t = 0; t < 3; ++t) coeff[t] = mask & (1u << t) ? 2 : e[t];
                coeff[witness] = e[witness];
                Tick constant = log_hi(P * std::popcount(mask)) - log_lo(e[witness] + 1);
                system[index++] = {witness, coeff, constant};
            }
            for (int t = 0; t < 2; ++t) {
                int w = order[t], v = order[t + 1];
                Triple coeff{};
                coeff[w] = e[w] + 2;
                coeff[v] = e[v] + 2;
                system[index++] = {w, coeff, log_hi(e[v] + 1) - log_lo(e[w] + 1)};
            }
        } while (std::next_permutation(order.begin(), order.end()));
    }

    bool possible(UInt xmin, UInt xmax) const {
        Wide ymin = std::max<Wide>({xmin + 1, UInt(e[1]) * (D / (e[1] + 1)) + 1,
                                    (threshold(xmax) - 1) * e[1] / (e[1] + 1) + 1});
        Wide ymax = 2 * threshold(xmin) + 5;
        if (ymin > ymax) return false;
        Bounds low{log_lo(xmin), log_lo(ymin), log_lo(ymin)};
        Bounds high{log_hi(xmax), log_hi(ymax), 0};
        Tick p_upper = log_hi(P);
        high[2] = ceil_quotient(p_upper + e[0] * high[0] + e[1] * high[1], e[2]);
        for (unsigned mask = 1; mask < 4; ++mask) {
            int dx = mask & 1 ? 2 : e[0];
            int dy = mask & 2 ? 2 : e[1];
            bool x_ok = !(mask & 1) || e[0] * low[0] >= p_upper + 2 * scale + dy * high[1];
            bool y_ok = !(mask & 2) || e[1] * low[1] >= p_upper + 2 * scale + dx * high[0];
            if (x_ok && y_ok)
                high[2] = std::min(high[2], p_upper + 2 * scale + dx * high[0] + dy * high[1]);
        }
        for (const auto& system : systems) if (consistent(system, low, high)) return true;
        return false;
    }

private:
    std::array<System, 6> systems{};

    Wide threshold(UInt x) const {
        Wide denominator = Wide(x - 1 - e[0] * K) * (x - 1) + K;
        return Wide(P) * (x - 1) * (x - 1) / denominator;
    }
};

bool is_prime(UInt p) {
    for (UInt d = 2; d <= p / d; ++d) if (p % d == 0) return false;
    return p >= 2;
}

int main(int argc, char** argv) {
    if (argc != 2) throw std::runtime_error("Supply the path for the (i,j,k,x) rows");
    for (unsigned i = 1; i < exact_logs.size(); ++i) {
        mpz_class power;
        mpz_ui_pow_ui(power.get_mpz_t(), i, scale);
        exact_logs[i] = mpz_sizeinbase(power.get_mpz_t(), 2) - 1;
    }
    std::ofstream rows(argv[1]);
    if (!rows) throw std::runtime_error("Cannot write row file");
    UInt profiles = 0, intervals = 0, possible_intervals = 0, viable_orders = 0, primes = 0;
    Triple e;
    while (std::cin >> e[0] >> e[1] >> e[2]) {
        ++profiles;
        Profile profile(e);
        UInt first = e[0] * profile.K + 1, last = 3 * profile.P + 1;
        UInt previous = 0, width = 1;
        bool viable = false;
        for (UInt lower = first; lower <= last;) {
            UInt upper = std::min(last, lower + width - 1);
            ++intervals;
            if (profile.possible(lower, upper)) {
                ++possible_intervals;
                viable = true;
                std::queue<std::pair<UInt, UInt>> pending;
                pending.push({lower, upper});
                while (!pending.empty()) {
                    auto [a, b] = pending.front();
                    pending.pop();
                    if (!profile.possible(a, b)) continue;
                    if (b - a > 10) {
                        UInt midpoint = a + (b - a) / 2;
                        pending.push({a, midpoint});
                        pending.push({midpoint + 1, b});
                    } else {
                        for (UInt x = a; x <= b; ++x) if (is_prime(x) && profile.possible(x, x)) {
                            rows << e[0] << ' ' << e[1] << ' ' << e[2] << ' ' << x << '\n';
                            ++primes;
                        }
                    }
                }
            }
            UInt next = previous + width;
            previous = width;
            width = next;
            lower = upper + 1;
        }
        viable_orders += viable;
    }
    rows.close();
    if (!std::cin.eof() || !rows) throw std::runtime_error("Incomplete input or output");
    std::cout << "Ordered profiles " << profiles << ", Fibonacci intervals " << intervals
              << ", surviving intervals " << possible_intervals << ", surviving orders "
              << viable_orders << ", prime-x cases " << primes << '\n';
}
