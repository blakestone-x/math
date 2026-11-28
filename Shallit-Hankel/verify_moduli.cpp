// Exhaust all finite words with no vanishing shifted Hankel minor for m=2,...,7.
// Compile with a C++17 compiler supporting signed 128-bit integers.
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>

using Integer = std::int64_t;
using Wide = __int128_t;
constexpr int capacity = 64;

class Enumeration {
    int modulus;
    bool prime;
    int inverse[8]{}, masks[8][8]{};
    Integer last[capacity][capacity]{};
    std::array<int, capacity> word{}, witness{};
    std::array<std::uint64_t, capacity> counts{};
    int longest = 0;

    int residue(Integer x) const {
        int r = int(x % modulus);
        return r < 0 ? r + modulus : r;
    }

    static Integer checked(Wide value) {
        if (value < std::numeric_limits<Integer>::min() ||
            value > std::numeric_limits<Integer>::max())
            throw std::overflow_error("minor exceeds verified integer storage");
        return Integer(value);
    }

    static Integer quotient(Integer left, Integer bottom, Integer middle, Integer divisor) {
        // The two products and their difference fit in signed 128-bit arithmetic
        // for signed 64-bit inputs. Use the cheaper 64-bit path when it fits.
        Integer p, q, d;
        if (!__builtin_mul_overflow(left, bottom, &p) &&
            !__builtin_mul_overflow(middle, middle, &q) &&
            !__builtin_sub_overflow(p, q, &d) &&
            d != std::numeric_limits<Integer>::min())
            return d / divisor;
        return checked((Wide(left)*bottom - Wide(middle)*middle) / divisor);
    }

    void visit(int length) {
        if (length >= capacity-1) throw std::runtime_error("increase capacity");
        ++counts[length];
        if (length > longest) { longest = length; witness = word; }

        const int max_order = (length+2)/2;
        Integer slope[capacity]{}, constant[capacity]{};
        slope[1] = 1;
        const int largest_digit = length < 2 ? (prime ? 1 : modulus/2) : modulus-1;
        int allowed = (1 << (largest_digit+1)) - 2;
        for (int order = 2; order <= max_order; ++order) {
            const auto *two_earlier = last[length-2];
            Integer left = two_earlier[order-1];
            Integer middle = last[length-1][order-1];
            Integer divisor = two_earlier[order-2];
            if (prime) {
                constant[order] = residue((left*constant[order-1] - middle*middle)
                                        * inverse[divisor]);
            } else {
                constant[order] = quotient(left, constant[order-1], middle, divisor);
            }
            slope[order] = left;
            allowed &= masks[residue(left)][residue(constant[order])];
            if (allowed == 0) return;
        }
        while (allowed) {
            const int digit = __builtin_ctz(static_cast<unsigned>(allowed));
            allowed &= allowed-1;
            word[length] = digit;
            last[length][0] = 1;
            for (int order=1; order<=max_order; ++order) {
                if (prime) last[length][order] = residue(slope[order]*digit + constant[order]);
                else last[length][order] = checked(Wide(slope[order])*digit + constant[order]);
            }
            visit(length+1);
        }
    }

public:
    Enumeration(int m) : modulus(m), prime(m==2 || m==3 || m==5 || m==7) {
        for (int a=0; a<m; ++a) for (int b=0; b<m; ++b) {
            if (a*b % m == 1) inverse[a] = b;
            for (int x=1; x<m; ++x)
                if ((a*x+b) % m != 0) masks[a][b] |= 1 << x;
        }
    }
    void run(int expected) {
        visit(0);
        if (longest != expected) throw std::runtime_error("unexpected maximum");
        std::uint64_t total = 0;
        for (int i=0; i<=longest; ++i) total += counts[i];
        std::cout << "modulus " << modulus << ", maximum " << longest
                  << ", normalized nodes " << total
                  << ", normalized extremizers " << counts[longest] << '\n';
        std::cout << "witness ";
        for (int i=0; i<longest; ++i) std::cout << witness[i];
        std::cout << '\n';
    }
};

int main(int argc, char **argv) {
    const int maxima[] = {0,0,2,4,24,22,42,52};
    const int chosen = argc==2 ? std::stoi(argv[1]) : 0;
    if (chosen && (chosen<2 || chosen>7)) throw std::invalid_argument("expected 2 through 7");
    for (int m=2; m<=7; ++m) if (!chosen || chosen==m)
        Enumeration(m).run(maxima[m]);
}
