"""Test the prime-power shifts by exact differentiation of powers at zero."""
def terms(kind, limit):
    # rows[n][k] is the n-th derivative at zero of f(x)^k.
    positive = kind in ("tan", "sinh")
    sign = 1 if positive else -1
    older = [1] + [0] * (limit + 1)
    current = [0, 1] + [0] * limit
    values = [0, 1]
    for n in range(2, limit + 1):
        new = [0] * (limit + 2)
        for k in range(1, n + 1):
            if kind in ("tan", "tanh"):
                new[k] = k * (current[k-1] + sign * current[k+1])
            else:
                lower = older[k-2] if k >= 2 else 0
                new[k] = k * (k-1) * lower + sign * k * k * older[k]
        values.append(sum(k**n * new[k] for k in range(1, n + 1)))
        older, current = current, new
    return values


if __name__ == "__main__":
    for kind in ("sinh", "sin", "tanh", "tan"):
        values = terms(kind, 165)
        for p, a in [(3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (3, 2),
                     (5, 2), (7, 2), (3, 3), (5, 3), (3, 4)]:
            modulus = p ** a
            phi = (p - 1) * p ** (a - 1)
            sign = -1 if kind in ("sin", "tan") and phi % 4 == 2 else 1
            for n in range(a, len(values) - phi):
                assert (values[n+phi] - sign * values[n]) % modulus == 0
                if kind == "tanh":
                    scaled = lambda j: values[j] * pow(4, 1-j, modulus)
                    assert (scaled(n+phi) - scaled(n)) % modulus == 0
        for n in range(1, len(values)):
            if kind in ("sinh", "sin"):
                assert values[n] % 2 == n % 2
            else:
                assert values[n] % (2 ** (n//2)) == 0
        print(kind, "verified through n =", len(values)-1)
