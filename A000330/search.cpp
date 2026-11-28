// Find integer triples of square pyramidal numbers with a specified integral sum.
// Build with c++ -std=c++17 -O3 search.cpp -o search
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <vector>

using Int = long long;
using Wide = __int128_t;

Int mod(Int a, Int m) {
    Int r = a % m;
    return r < 0 ? r + m : r;
}

Int inverse(Int a, Int m) {
    Int b = m, x = 1, y = 0;
    while (b) {
        Int q = a / b;
        Int next = a - q * b;
        a = b;
        b = next;
        next = x - q * y;
        x = y;
        y = next;
    }
    return mod(x, m);
}

std::vector<int> smallest_factors(int bound) {
    std::vector<int> factors(bound + 1);
    for (int p = 2; p <= bound; ++p) {
        if (factors[p]) continue;
        for (int multiple = p; multiple <= bound; multiple += p)
            if (!factors[multiple]) factors[multiple] = p;
    }
    return factors;
}

int main(int argc, char** argv) {
    if (argc != 5) {
        std::cerr << "usage: search target max_abs_u max_abs_Z max_prime_factor\n";
        return 2;
    }
    Int target = std::atoll(argv[1]);
    int bound = std::atoi(argv[2]), z_bound = std::atoi(argv[3]), prime_bound = std::atoi(argv[4]);
    if (bound < 1 || bound > 5000000 || z_bound < 1 || z_bound > 500000000 ||
        prime_bound < 2 || target < -1000000000LL || target > 1000000000LL) return 2;
    auto factors = smallest_factors(bound);
    std::vector<std::vector<int>> roots(bound + 1);
    roots[1] = {0};
    bool square_mod_256[256] = {};
    for (int i = 0; i < 256; ++i) square_mod_256[i*i % 256] = true;

    // roots[m] contains Z with m dividing 24*target + Z - Z^3.
    auto is_root = [&](Int z, int m) {
        return mod(24*target + z - (z*z % m)*z, m) == 0;
    };
    for (int m = 1; m <= bound; ++m) {
        if (m > 1) {
            int p = factors[m];
            if (p > prime_bound) continue;
            int q = 1, rest = m;
            while (rest % p == 0) {
                q *= p;
                rest /= p;
            }
            if (rest != 1) {
                int inv = inverse(q, rest);
                for (int x : roots[q])
                    for (int y : roots[rest])
                        roots[m].push_back(x + q * mod(Int(y-x)*inv, rest));
            } else if (m == p) {
                for (int a = 0; a < p; ++a)
                    if (is_root(a, m)) roots[m].push_back(a);
            } else {
                for (int a : roots[m/p])
                    for (int z = a; z < m; z += m/p)
                        if (is_root(z, m)) roots[m].push_back(z);
            }
        }

        for (int residue : roots[m]) {
            Int first = -z_bound + mod(residue + Int(z_bound), m);
            Int step = m;
            if (m % 2) {
                if (first % 2 == 0) first += m;
                step *= 2;
            } else if (first % 2 == 0) continue;
            for (Int z = first; z <= z_bound; z += step) {
                // u = x+y+1, v = x-y, Z = 2c+1. A solution must have
                // 6*u*v^2 = 24*target + Z - Z^3 - 2*u^3 + 2*u.
                Wide quotient = (Wide(24)*target + z - Wide(z)*z*z) / m;
                Int sign = quotient < 0 ? -1 : 1;
                Wide six_square = sign*quotient - Wide(2)*m*m + 2;
                if (six_square < 0 || six_square % 6) continue;
                Wide square = six_square / 6;
                if (!square_mod_256[int(square % 256)]) continue;
                Int v = static_cast<Int>(std::sqrt(static_cast<long double>(square)));
                while (Wide(v)*v > square) --v;
                while (Wide(v+1)*(v+1) <= square) ++v;
                if (Wide(v)*v != square || (m+v)%2 != 1) continue;
                Int u = sign*m;
                std::cout << target << ' ' << (u+v-1)/2 << ' ' << (u-v-1)/2 << ' ' << (z-1)/2 << '\n';
                return 0;
            }
        }
    }
    std::cerr << "No witness in these search bounds.\n";
    return 1;
}
