"""Check the generating function by enumerating compositions directly."""


def by_cuts(n):
    total = ones = 0
    for cuts in range(1 << (n - 1)):
        endpoints = [0] + [j for j in range(1, n) if cuts & (1 << (j-1))] + [n]
        parts = [b - a for a, b in zip(endpoints, endpoints[1:])]
        smallest = min(parts)
        value = sum(i for i, part in enumerate(parts, 1) if part == smallest)
        total += value
        if smallest == 1:
            ones += value
    return total, ones


def by_series(n):
    total = 0
    for m in range(1, n + 1):
        # Multiply three times by 1/(1 - sum_{j>=m} x^j).
        coeffs = [1] + [0] * (n-m)
        for _ in range(3):
            for i in range(m, n-m+1):
                coeffs[i] += sum(coeffs[:i-m+1])
        total += coeffs[n-m]
    return total


if __name__ == "__main__":
    for n in range(1, 19):
        total, ones = by_cuts(n)
        assert by_series(n) == total
        if n >= 2:
            assert 32 * ones == (n+1) * (n+6) * 2**n
    print("Direct counts match the generating function through n=18.")
