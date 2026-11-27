"""Independent finite-window checks using the literal one-based list deletion."""
from itertools import accumulate
from random import Random


def literal(mask, limit):
    items = list(range(1, limit + 1))
    leaders = []
    while items:
        leaders.append(items[0])
        items = [x for j, x in enumerate(items[1:], 1) if j not in mask]
    return leaders


def rank_transform(mask, limit):
    mask_rank = [0] + list(accumulate(i in mask for i in range(1, limit + 1)))
    rank = [0]
    for n in range(limit):
        rank.append(1 + rank[n - mask_rank[n]])
    return [i for i in range(1, limit + 1) if rank[i] > rank[i - 1]]


def orbit(step, limit):
    n = 1
    while n <= limit:
        yield n
        n = step(n)


def check_rates(mask, limit, max_k):
    for t in range(1, 2 * max_k + 2):
        seq = literal(mask, limit)
        assert seq == rank_transform(mask, limit)
        k = min((t + 1) // 2, max_k)
        assert seq[:k] == [j * (j + 1) // 2 for j in range(1, k + 1)]
        mask = set(seq)


def main():
    for bits in range(2 ** 11):
        mask = {i + 1 for i in range(11) if bits >> i & 1}
        check_rates(mask, 11, 4)
    rng = Random(152009)
    for chance in (0.01, 0.15, 0.5, 0.85, 0.99):
        mask = {i for i in range(1, 202) if rng.random() < chance}
        check_rates(mask, 201, 19)
    limit = 1200
    for d in range(2, 26):
        for c in range(1, d + 1):
            mask = set(range(c, limit + 1, d))
            expected = orbit(lambda s: 1 + s + (s + d - c - 1) // (d - 1), limit)
            assert literal(mask, limit) == list(expected)
        maxima = {}
        for start in range(limit + 1):
            t, x = 0, start
            while x:
                x = x * (d - 1) // d
                t += 1
            maxima[t] = start
        # The largest occupied bin may be clipped by the right endpoint.
        last = max(maxima)
        actual = [maxima[t] for t in range(1, last)]
        assert actual == literal(set(range(d - 1, limit + 1, d)), limit)[:last - 1]
    rank = [0]
    for n in range(10000):
        rank.append(1 + rank[2 * n // 3])
    jumps = [n for n in range(1, len(rank)) if rank[n] > rank[n - 1]]
    assert jumps == literal(set(range(1, 10001, 3)), 10000)
    print("PASS: literal sieve vs rank rule on all 2,048 masks in [1,11]")
    print("PASS: stabilization bounds, every residue for moduli 2..25, and stopping maxima")
    print("PASS: first 10,000 positive indices of the A214972 jump identity")


if __name__ == "__main__":
    main()
