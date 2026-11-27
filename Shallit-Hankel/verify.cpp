// Reproduce the all-shifts bound for Shallit's four-symbol Hankel problem.
// Compile with g++ -O3 -std=c++17 verify.cpp -o verify
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::string;
using Residue = std::uint64_t;
using Wide = __uint128_t;

constexpr Residue modulus = (Residue{1} << 61) - 1;
const std::array<Word, 5> rule = {"", "12", "23", "14", "32"};

void require(bool condition, const std::string& message) {
    if (!condition) throw std::runtime_error(message);
}

Word substitute(const Word& word) {
    Word result;
    result.reserve(2 * word.size());
    for (char letter : word) result += rule[letter - '0'];
    return result;
}

std::set<Word> legal_pairs() {
    Word prefix = "1";
    for (int step = 0; step < 5; ++step) prefix = substitute(prefix);
    std::set<Word> pairs;
    for (std::size_t i = 1; i < prefix.size(); ++i)
        pairs.insert(prefix.substr(i - 1, 2));

    // Every symbol pair of an image is inside one letter image or crosses
    // a boundary between images of adjacent letters.
    for (int letter = 1; letter <= 4; ++letter)
        require(pairs.count(rule[letter]) == 1, "Missing internal pair");
    for (const auto& pair : pairs) {
        const Word boundary = substitute(pair).substr(1, 2);
        require(pairs.count(boundary) == 1, "Pair set is not closed");
    }
    return pairs;
}

Residue multiply(Residue a, Residue b) {
    const Wide product = Wide{a} * b;
    const Residue folded = Residue(product >> 61) + (Residue(product) & modulus);
    return folded >= modulus ? folded - modulus : folded;
}

Residue power(Residue base, Residue exponent) {
    Residue result = 1;
    while (exponent) {
        if (exponent & 1) result = multiply(result, base);
        base = multiply(base, base);
        exponent >>= 1;
    }
    return result;
}

// Invert a row using one modular power, prefix products, and a backward pass.
void invert_row(const std::vector<Residue>& row, std::size_t size,
                std::vector<Residue>& inverse, std::vector<Residue>& prefix) {
    Residue product = 1;
    for (std::size_t i = 0; i < size; ++i) {
        prefix[i] = product;
        product = multiply(product, row[i]);
    }
    Residue tail = power(product, modulus - 2);
    require(multiply(product, tail) == 1, "Row contains a non-unit");
    for (std::size_t i = size; i-- > 0;) {
        inverse[i] = multiply(prefix[i], tail);
        tail = multiply(tail, row[i]);
    }
}

// Direct signed sum over permutations, grouped by the columns already used.
// Used for orders <= 8 only. 8! * 4^8 bounds all absolute intermediate sums.
Residue direct_determinant(const Word& word, std::size_t start, unsigned order) {
    require(order <= 8, "Direct integer check exceeds its proved range");
    const unsigned size = 1U << order;
    std::vector<std::int64_t> partial(size);
    partial[0] = 1;
    for (unsigned mask = 0; mask + 1 < size; ++mask) {
        unsigned used = __builtin_popcount(mask);
        for (unsigned col = 0; col < order; ++col) {
            const unsigned bit = 1U << col;
            if (mask & bit) continue;
            const bool odd = __builtin_popcount(mask >> (col + 1)) & 1;
            const auto term = partial[mask] * (word[start + used + col] - '0');
            partial[mask | bit] += odd ? -term : term;
        }
    }
    const auto d = partial.back();
    return d < 0 ? modulus - Residue(-d) : Residue(d);
}

std::uint64_t check_word(const Word& word, unsigned max_order, bool direct) {
    const std::size_t length = word.size();
    require(2 * max_order - 1 <= length, "Word too short");
    std::vector<Residue> previous(length), current(length), inverse(length, 1),
                         prefix(length);
    for (std::size_t i = 0; i < length; ++i) {
        previous[i] = word[i] - '0';
        require(previous[i] != 0, "Zero at order one");
        if (direct) require(previous[i] == direct_determinant(word, i, 1),
                            "Order-one direct check failed");
    }

    // At order r, previous holds order r-1 and inverse holds the reciprocals
    // at order r-2. The empty determinant at order zero is one.
    std::uint64_t checked = length;
    for (unsigned r = 2; r <= max_order; ++r) {
        const std::size_t count = length - 2*r + 2;
        for (std::size_t i = 0; i < count; ++i) {
            const auto outside = multiply(previous[i], previous[i + 2]);
            const auto middle = multiply(previous[i + 1], previous[i + 1]);
            const auto difference = outside >= middle ? outside - middle
                                                       : modulus - (middle - outside);
            current[i] = multiply(difference, inverse[i + 2]);
            if (current[i] == 0)
                throw std::runtime_error("Zero modulo the modulus at order "
                                         + std::to_string(r) + ", offset " + std::to_string(i));
            if (direct) require(current[i] == direct_determinant(word, i, r),
                                "Independent signed-permutation check failed");
        }
        checked += count;
        if (r < max_order) invert_row(previous, count + 2, inverse, prefix);
        previous.swap(current);
    }
    return checked;
}

int main() {
    const auto pairs = legal_pairs();
    require(pairs.size() == 9, "Unexpected pair count");
    std::uint64_t small_count = 0, full_count = 0;
    for (const auto& pair : pairs) {
        Word word = pair;
        for (int j = 0; j < 4; ++j) word = substitute(word);
        small_count += check_word(word, 8, true);
        for (int j = 4; j < 13; ++j) word = substitute(word);
        full_count += check_word(word, 4096, false);
        std::cout << pair << " passed\n";
    }
    require(small_count == 1800, "Unexpected direct check count");
    require(full_count == 453021696, "Unexpected main check count");
    std::cout << "Independent direct checks: " << small_count
              << "\nNonzero modular determinants: " << full_count << '\n';
}
