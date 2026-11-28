// Verify the finite-field irreducibility certificates in primes.txt.
// Build with c++ -O2 -std=c++17 verify.cpp -o verify, then run ./verify primes.txt.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using Polynomial = std::vector<int>;  // coefficients from the constant term up
using Wide = std::int64_t;
constexpr int limit = 2048;

bool is_prime(int n) {
    if (n < 2) return false;
    for (int d = 2; d * d <= n; ++d) {
        if (n % d == 0) return false;
    }
    return true;
}

int next_prime(int n) {
    do { ++n; } while (!is_prime(n));
    return n;
}

int residue(Wide value, int p) {
    value %= p;
    return static_cast<int>(value < 0 ? value + p : value);
}

int field_power(Wide base, int exponent, int p) {
    Wide result = 1;
    while (exponent > 0) {
        if (exponent % 2) result = result * base % p;
        base = base * base % p;
        exponent /= 2;
    }
    return static_cast<int>(result);
}

void trim(Polynomial& f) {
    while (!f.empty() && f.back() == 0) f.pop_back();
}

void make_monic(Polynomial& f, int p) {
    int inverse = field_power(f.back(), p - 2, p);
    for (int& coefficient : f) coefficient = residue(Wide(coefficient) * inverse, p);
}

Polynomial remainder(std::vector<Wide> work, const Polynomial& monic, int p) {
    const int degree = static_cast<int>(monic.size()) - 1;
    for (int k = static_cast<int>(work.size()) - 1; k >= degree; --k) {
        const int multiplier = residue(work[k], p);
        for (int j = 0; j < degree; ++j) {
            work[k - degree + j] -= Wide(multiplier) * monic[j];
        }
    }
    Polynomial answer;
    for (int j = 0; j < degree && j < static_cast<int>(work.size()); ++j) {
        answer.push_back(residue(work[j], p));
    }
    trim(answer);
    return answer;
}

Polynomial multiply_mod(const Polynomial& a, const Polynomial& b,
                        const Polynomial& modulus, int p) {
    if (a.empty() || b.empty()) return {};
    std::vector<Wide> product(a.size() + b.size() - 1);
    for (std::size_t i = 0; i < a.size(); ++i) {
        for (std::size_t j = 0; j < b.size(); ++j) {
            product[i + j] += Wide(a[i]) * b[j];
        }
    }
    return remainder(product, modulus, p);
}

Polynomial frobenius(Polynomial base, const Polynomial& modulus, int p) {
    Polynomial result{1};
    for (int exponent = p; exponent > 0; exponent /= 2) {
        if (exponent % 2) result = multiply_mod(result, base, modulus, p);
        if (exponent > 1) base = multiply_mod(base, base, modulus, p);
    }
    return result;
}

bool coprime(Polynomial a, Polynomial b, int p) {
    while (!b.empty()) {
        if (b.size() == 1) return true;
        make_monic(b, p);
        Polynomial r = remainder(std::vector<Wide>(a.begin(), a.end()), b, p);
        a = std::move(b);
        b = std::move(r);
    }
    return a.size() == 1;
}

Polynomial sun_polynomial(int n, int p) {
    // The verified inequality p > 2n makes every factorial here invertible.
    std::vector<Wide> fact(2 * n + 1), inverse_fact(2 * n + 1);
    fact[0] = 1;
    for (int j = 1; j <= 2 * n; ++j) fact[j] = fact[j - 1] * j % p;
    inverse_fact[2 * n] = field_power(fact[2 * n], p - 2, p);
    for (int j = 2 * n; j > 0; --j) inverse_fact[j - 1] = inverse_fact[j] * j % p;
    const auto binom = [&](int a, int b) {
        return fact[a] * inverse_fact[b] % p * inverse_fact[a - b] % p;
    };
    Polynomial result;
    for (int j = 0; j <= n / 2; ++j) {
        Wide first = binom(n, j);
        result.push_back(residue(first * first % p * binom(2 * n - 2 * j, n), p));
    }
    make_monic(result, p);
    return result;
}

bool excludes_small_factors(int n, int p, int bound) {
    Polynomial f = sun_polynomial(n, p);
    Polynomial x_power{0, 1};
    for (int i = 1; i <= bound; ++i) {
        x_power = frobenius(x_power, f, p);  // X^(p^i) modulo f
        Polynomial difference = x_power;
        if (difference.size() < 2) difference.resize(2);
        difference[1] = residue(difference[1] - 1, p);
        trim(difference);
        if (!coprime(f, difference, p)) return false;
    }
    return true;
}
}

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Usage: verify primes.txt\n";
        return 1;
    }
    std::ifstream certificates(argv[1]);
    if (!certificates) return 1;
    int by_family = 0;
    int by_certificate = 0;
    for (int n = 2; n <= limit; ++n) {
        const int degree = n / 2;
        const int dominant = n - (next_prime(n) - 1) / 2;
        if (2 * dominant <= degree || dominant > degree) {
            std::cerr << "Invalid dominant-factor bound at n=" << n << '\n';
            return 1;
        }
        if (is_prime(n - 1) || is_prime(n) || is_prime(n + 1) || is_prime(n + 2)) {
            ++by_family;
            continue;
        }
        int index, p;
        // p <= 65535 and degree <= 1024 keep every convolution and division
        // accumulator below 3 * (degree+1) * 65535^2 in absolute value.
        if (!(certificates >> index >> p) || index != n || p <= 2 * n || p > 65535 ||
            !is_prime(p) || !excludes_small_factors(n, p, degree - dominant)) {
            std::cerr << "Invalid certificate at n=" << n << '\n';
            return 1;
        }
        ++by_certificate;
    }
    std::string extra;
    if (certificates >> extra) {
        std::cerr << "Unexpected extra certificate data\n";
        return 1;
    }
    std::cout << "Verified n=2.." << limit << ": " << by_family
              << " by the prime-index theorem and " << by_certificate
              << " by modular certificates.\n";
}
