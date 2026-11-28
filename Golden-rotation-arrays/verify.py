"""Independent exact-integer checks for the two Wythoff manuscripts."""
from collections import Counter
from math import gcd, isqrt, lcm, prod


def lower(n):
    return (n + isqrt(5 * n * n)) // 2


def difference(n):
    """Evaluate the published arrays directly. Rows and columns start at 1."""
    twice_row = 2 * n - 1
    first = n + (twice_row + isqrt(5 * twice_row**2)) // 4
    second = (first + 1 + isqrt(5 * first**2)) // 2
    return 2 * lower(n) + n - 1 - second


def golden_sign(a, b):
    """Sign of a+b*beta, by comparing two integer squares."""
    x = 2 * a - b
    if b < 0:
        return -golden_sign(-a, -b)
    if b == 0:
        return (x > 0) - (x < 0)
    if x >= 0:
        return 1
    return (5 * b * b > x * x) - (5 * b * b < x * x)


def row_gaps(limit):
    indices = {s: [] for s in (0, 1, -1)}
    for n in range(1, limit + 1):
        tag = difference(n)
        assert tag == 2 * (lower(n) - n) - (lower(2 * n - 1) - (2 * n - 1))
        indices[tag].append(n)

    gap_lists = {}
    for s, expected in [(0, {1, 2, 3}), (1, {2, 3, 5}), (-1, {3, 5, 8})]:
        rows = indices[s]
        gaps = [b - a for a, b in zip(rows, rows[1:])]
        counts = Counter(gaps)
        assert set(counts) == expected
        gap_lists[s] = gaps
        print(f"sign {s:+d}, {len(rows):,} rows; successive gaps {dict(sorted(counts.items()))}")
    mapped = [lower(m) for m in indices[1] if lower(m) <= limit]
    assert mapped == indices[-1]
    translate = {2: 3, 3: 5, 5: 8}
    assert [translate[g] for g in gap_lists[1][:len(mapped)-1]] == gap_lists[-1]
    print(f"paired lists agree through row {limit:,} ({len(mapped):,} pairs)")


def prime_sieve(limit):
    primes = bytearray(b'\x01') * (limit + 1)
    primes[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if primes[p]:
            primes[p*p::p] = bytes((limit - p*p) // p + 1)
    return primes


def columns(limit, primes):
    # Represent each power of beta as a pair (a,b) for a+b*beta.
    powers = [(1, 0)]
    for _ in range(70):
        a, b = powers[-1]
        powers.append((b, a - b))
    seen = bytearray(limit + 1)
    prime_counts = Counter()
    m = 1
    while True:
        a = lower(m)
        x, y = a + m - 1, 2 * a + m - 1
        if x > limit:
            break
        k = 1
        while x <= limit:
            assert seen[x] == 0
            seen[x] = k
            small, large = powers[k + 2], powers[k]
            if k % 2:
                left, right = (1-large[0], -large[1]), (1-small[0], -small[1])
            else:
                left, right = small, large
            phase = (x - lower(x), x)
            assert golden_sign(phase[0]-left[0], phase[1]-left[1]) == 1
            assert golden_sign(right[0]-phase[0], right[1]-phase[1]) == 1
            if primes[x]:
                prime_counts[k] += 1
            x, y = y, x + y
            k += 1
        m += 1
    assert all(seen[1:])
    assert sum(prime_counts.values()) == sum(primes)
    print(f"exact column intervals agree with array enumeration for all {limit:,} integers")
    print(f"{sum(primes):,} primes; counts in columns 1 to 6: {[prime_counts[k] for k in range(1, 7)]}")


def primitive_rows(limit, primes):
    counts = Counter()
    run = longest = 0
    first_five = None
    for m in range(1, limit + 1):
        u, a = m - 1, lower(m)
        g = gcd(a + u, 2 * a + u)
        assert g == gcd(u, a)
        counts[g] += 1
        run = run + 1 if g == 1 else 0
        longest = max(longest, run)
        if run == 5 and first_five is None:
            first_five = m - 4
        if u > 3 and primes[u]:
            assert g == 1
    assert (first_five, longest) == (36, 5)
    print(f"gcd counts in rows 1 to {limit:,}, g=1 to 6: {[counts[g] for g in range(1, 7)]}")
    print(f"first longest primitive run: {first_five} to {first_five+4}")

    # Test the offset, spacing and divisor counts directly on multiples of d.
    for d in range(1, 1001):
        previous = None
        count = 0
        for u in range(d, limit + 1, d):
            if lower(u + 1) % d:
                continue
            assert d*d <= 10*u
            if previous is not None:
                assert d*d <= 5*(u - previous)
            previous = u
            count += 1
        assert count * d*d <= 10*limit
    print("divisor offset, spacing and counting bounds checked for d=1 to 1,000")


def covering_certificate():
    # Use Vsemirnov's original residues, independent of the shifted Lean table.
    triples = [
        (3,4,3), (2,3,1), (5,5,4), (7,8,5), (17,9,2), (11,10,6),
        (47,16,9), (19,18,14), (61,15,12), (23,24,17), (107,36,8),
        (31,30,0), (1103,48,33), (181,90,80), (41,20,18), (541,90,62),
        (2521,60,48),
    ]
    seq = [106276436867, 35256392432]
    fib = [0, 1]
    for _ in range(808):
        seq.append(sum(seq[-2:]))
        fib.append(sum(fib[-2:]))
    m = seq[53] + 1
    u, a = m - 1, lower(m)
    assert m == 5381684723742272612570
    assert a == seq[54] and gcd(u, a) == 1
    assert (a+u, 2*a+u) == (14089433523493357901064, 22797182323244443189559)
    assert lcm(*(t for _, t, _ in triples)) == 720
    assert prod(s for s, _, _ in triples) == 1821895895860356790898731230
    for s, t, r in triples:
        assert all(s % j for j in range(2, isqrt(s) + 1))
        assert fib[t] % s == 0 and seq[r] % s == 0
    for k in range(720):
        val = fib[k+1]*a + fib[k]*u
        assert val == seq[k+54]
        assert any((k+54) % t == r and val % s == 0 and 1 < s < val for s, t, r in triples)
    print(f"row {m:,}: coprime seeds, exact Wythoff embedding and all 720 covering residues verified")


if __name__ == "__main__":
    limit = 1_000_000
    row_gaps(250_000)
    primes = prime_sieve(limit)
    columns(limit, primes)
    primitive_rows(limit, primes)
    covering_certificate()
