#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>

// All arithmetic on a Wide value takes place modulo 2^128.
using Wide = unsigned __int128;

Wide inverse_odd(unsigned value) {
    Wide result = 1;
    for (int step = 0; step < 7; ++step) {
        result *= 2 - Wide(value) * result;
    }
    if (result * value != 1) throw std::runtime_error("incorrect modular inverse");
    return result;
}

void verify_row(int q) {
    const unsigned size = 1U << q;
    const unsigned n = size - 1;
    const int h = 3*q - 3;
    const int last = 3*q - 4;
    std::array<Wide, 64> sums{};
    Wide binom = 1;
    for (unsigned k = 0; k < size/2; ++k) {
        if (k != 0) {
            const int zeros = __builtin_ctz(k);
            // binom(n,k)/binom(n,k-1) = (size/k)-1 in Z_2.
            binom *= Wide(size >> zeros)*inverse_odd(k >> zeros) - 1;
        }
        Wide power = binom;
        for (int m = 1; m <= last; ++m) {
            power *= power;
            sums[m] += 2*binom*power;
        }
    }
    const Wide row_sum = n < 128 ? (Wide(1) << n) : Wide(0);
    for (int m = 1; m <= last; ++m) {
        const int shift = h + m;
        const Wide difference = sums[m] - row_sum;
        const unsigned expected_unit = m == 1 ? 1 : m == 2 ? 7 : 3;
        if ((difference & ((Wide(1) << shift)-1)) != 0 ||
            ((difference >> shift) & 7) != expected_unit) {
            throw std::runtime_error("binomial row failed at q=" + std::to_string(q)
                                     + ", m=" + std::to_string(m));
        }
    }
    std::cout << "q=" << q << "  n=" << n << "  checked exponents 1.." << last
              << "  unit residues 1,7,3,...,3 mod 8\n";
}

int main() {
    for (int q = 4; q <= 22; ++q) verify_row(q);
}
