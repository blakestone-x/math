"""Compare backward gap screening against explicit forward cycles.

Using small subsets of screening primes yields many positive controls, even
at r where no genuine prime cycle exists.
"""
import json
from pathlib import Path
from squarefree import distinct_orders, divisors, multiplicative_partitions, screened_gaps


def gaps_with_last_longest(total, length):
    def generate(left, prefix):
        if len(prefix) == length - 1:
            if left >= max(prefix, default=0):
                yield tuple(prefix + [left])
            return
        for g in range(left + 1):
            yield from generate(left - g, prefix + [g])
    yield from generate(total, [])


def avoids_primes(coefficients, gaps, moduli):
    # Expand the coefficients, then obtain each cycle entry independently by
    # summing the formula at that rotation; no division modulo a prime.
    c = []
    for value, gap in zip(coefficients, gaps):
        c.extend([value] + [1] * gap)
    for i in range(len(c)):
        rotation = c[i:] + c[:i]
        entry = 0
        prefix = 1
        for j, factor in enumerate(rotation):
            entry += (1 << (len(c) - j - 1)) * prefix
            prefix *= factor
        if any(entry % q == 0 for q in moduli):
            return False
    return True


def run():
    data = json.loads(Path(__file__).with_name('factors.json').read_text())
    kept = rejected = 0
    for r in (2, 3, 5, 7, 9, 11, 13, 15):
        factors = data['orders'][str(r)]
        for part in multiplicative_partitions(2**r + 1, divisors(factors)):
            for cs in distinct_orders(part):
                for group in ([3], [5], [3, 5, 11]):
                    logs = {q: {pow(2, j, q): j for j in range(q-1)} for q in group}
                    inv = {q: [pow(2, -j, q) for j in range(r+1)] for q in group}
                    screened = set(screened_gaps(r, cs, group, logs, inv))
                    direct = set()
                    for gaps in gaps_with_last_longest(r - len(cs), len(cs)):
                        active = [q for q in group if q-2 <= gaps[-1]]
                        if avoids_primes(cs, gaps, active):
                            direct.add(gaps)
                            kept += 1
                        else:
                            rejected += 1
                    assert screened == direct, (r, cs, group, direct ^ screened)
    print(f'All modular comparisons agree: {kept} accepted and {rejected} rejected.')


if __name__ == '__main__':
    run()
