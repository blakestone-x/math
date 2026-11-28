"""Evaluate Wei's signed smooth-gap sequences on the certified radical domain."""
import argparse
import gzip
import math
from collections import defaultdict
from pathlib import Path

PRIMES = {5: (2, 3, 5), 7: (2, 3, 5, 7)}
LIMIT = 10_000_000
CATALOGUE = Path(__file__).with_name("catalogue.tsv.gz")


def rough_part(n, primes):
    """Remove every factor from primes. The input is positive."""
    if n < 1:
        raise ValueError("a positive integer is required")
    for prime in primes:
        while n % prime == 0:
            n //= prime
    return n


def radical_within(n, limit):
    """Whether the product of the distinct prime factors of n is at most limit."""
    product = 1
    factor = 2
    while factor * factor <= n and product * factor <= limit:
        if n % factor == 0:
            product *= factor
            while n % factor == 0:
                n //= factor
        factor = 3 if factor == 2 else factor + 2
    return product * n <= limit


def smooth_numbers(primes, limit):
    values = [1] if limit >= 1 else []
    for prime in primes:
        expanded = []
        for value in values:
            while value <= limit:
                expanded.append(value)
                value *= prime
        values = expanded
    return sorted(values)


def read_catalogue():
    rows = {p: defaultdict(list) for p in PRIMES}
    with gzip.open(CATALOGUE, "rt", encoding="ascii") as handle:
        if handle.readline().rstrip() != "bound\trough\tgap\tendpoint":
            raise ValueError("unexpected column names")
        for line in handle:
            p, rough, gap, endpoint = map(int, line.split())
            rows[p][rough].append((gap, endpoint))
    return rows


def value(rows, p, n):
    primes = PRIMES[p]
    rough = rough_part(n, primes)
    if not radical_within(rough, LIMIT // math.prod(primes)):
        raise ValueError("this prime support exceeds the certified radical bound")
    return max((u * (n // d) for d, u in rows[p].get(rough, ()) if n % d == 0),
               default=0)


def prefix(rows, p, limit):
    if not 1 <= limit <= LIMIT // math.prod(PRIMES[p]):
        raise ValueError("prefix length is outside the certified interval")
    result = [0] * (limit + 1)
    factors = smooth_numbers(PRIMES[p], limit)
    for block in rows[p].values():
        for d, u in block:
            for h in factors:
                n = d * h
                if n > limit:
                    break
                result[n] = max(result[n], u * h)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bound", type=int, choices=PRIMES)
    parser.add_argument("indices", nargs="*", type=int)
    parser.add_argument("--prefix", type=int, metavar="N", help="print the first N values, in b-file format")
    args = parser.parse_args()
    if bool(args.indices) == (args.prefix is not None):
        parser.error("supply one or more indices, or select --prefix N")
    rows = read_catalogue()
    try:
        if args.prefix is not None:
            for n, u in enumerate(prefix(rows, args.bound, args.prefix)[1:], 1):
                print(n, u)
        else:
            for n in args.indices:
                print(n, value(rows, args.bound, n))
    except ValueError as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
