"""Independent finite checks of the greedy rule and the periodic-cut argument."""
from hashlib import sha256
from itertools import count


def prime_masks(limit):
    masks = [0] * (limit + 1)
    bit = 1
    for p in range(2, limit + 1):
        if masks[p] == 0:
            for multiple in range(p, limit + 1, p):
                masks[multiple] |= bit
            bit <<= 1
    return masks


def prime_walk(k, length, masks):
    used = bytearray(len(masks))
    answer = [1]
    used[1] = 1
    smallest = 2
    for _ in range(1, length):
        previous = masks[answer[-1]]
        for candidate in range(smallest, len(masks)):
            if not used[candidate] and (previous | masks[candidate]).bit_count() >= k:
                break
        else:
            raise ValueError("Increase the sieve limit for this prefix")
        answer.append(candidate)
        used[candidate] = 1
        while used[smallest]:
            smallest += 1
    return answer


def digest(values):
    return sha256(",".join(map(str, values)).encode()).hexdigest()


def cut_trials():
    trials = 0
    for period in range(1, 11):
        for mask in range(1 << period):
            anchors = [u for u in range(period) if mask >> u & 1]
            if 2 * len(anchors) <= period:
                continue
            j = max(range(len(anchors)), key=lambda i: 2 * i - anchors[i])
            first_cut = anchors[j]

            def universal(u):
                return bool(mask >> (u % period) & 1)

            for mode in range(4):
                def allowed(x, y):
                    if universal(x) or universal(y):
                        return True
                    if mode == 0:
                        return False
                    if mode == 1:
                        return True
                    if mode == 2:
                        return (x * y + x + y) % 5 <= 1
                    return (13 * x + 7 * y + x * y) % 11 <= 3

                prefix = set()
                previous = None
                for position in range(5 * period + 1):
                    label = next(y for y in count() if y not in prefix and
                                 (previous is None or allowed(previous, y)))
                    if position >= first_cut and (position - first_cut) % period == 0:
                        assert prefix == set(range(position)) and label == position
                    assert abs(label - position) <= period
                    prefix.add(label)
                    previous = label
                trials += 1
    return trials


def main():
    masks = prime_masks(80000)
    walks = {k: prime_walk(k, 7000, masks) for k in range(1, 7)}
    for k, walk in walks.items():
        assert len(set(walk)) == len(walk)
        assert all((masks[x] | masks[y]).bit_count() >= k for x, y in zip(walk, walk[1:]))
    assert walks[1] == list(range(1, 7001))
    assert walks[2] == [1, 6, 2, 3, 4, 5, *range(7, 7001)]
    # Comma-separated decimal values of the 53 published terms in OEIS A285655.
    assert digest(walks[6][:53]) == "463944be4b741d0ec15edc73d97a2ce3a63370bb7e606a1966979cb34300d87f"
    fixed = [i for i, v in enumerate(walks[6], 1) if i == v]
    assert fixed == [1, 39, 1344, 1350, 3556, 3560, 5738, 6974]
    # The first 60 listed terms in OEIS A285487.
    reference = [1,2310,2,1155,4,1365,6,385,12,455,18,595,22,105,26,165,14,195,28,
                 255,38,210,11,390,7,330,13,420,17,462,5,546,10,231,20,273,30,77,
                 60,91,66,35,78,55,42,65,84,85,114,70,33,130,21,110,39,140,51,154,15,182]
    assert walks[5][:len(reference)] == reference
    bad = {n for n in range(2, 79999) if (masks[n] | masks[n + 1]).bit_count() < 3}
    predicted = set()
    for e in range(1, 18):
        power = 2**e
        for n in (power - 1, power):
            if 2 <= n < 79999:
                odd = n if n % 2 else n + 1
                if odd == 9 or all(odd % d for d in range(2, int(odd**0.5) + 1)):
                    predicted.add(n)
    assert bad == predicted
    print("Greedy prefixes: 7,000 terms for each k from 1 through 6.")
    print("Matched 53 published A285655 terms, 60 A285487 terms, and all eight reported fixed positions through 7,000.")
    print(f"Classified {len(bad)} inadmissible consecutive pairs for k=3 on 2 <= n < 79,999.")
    print(f"Verified every predicted cut in {cut_trials():,} periodic graph trials.")


if __name__ == "__main__":
    main()
