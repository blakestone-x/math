"""Run a second end-to-end proof of the A245211 three-prime classification."""
from array import array
from bisect import bisect_left, bisect_right
from functools import lru_cache
from itertools import permutations
from math import gcd, isqrt
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory

PROFILE_MODULI = (64, 81, 49, 25, 43, 41, 37, 32, 31, 29, 27, 23,
                  19, 17, 16, 13, 11, 9, 8, 7, 5, 3)
PAIR_MODULI = (16, 27, 25, 49, 11, 13, 17, 19, 23, 29, 31, 37,
               41, 43, 47, 53, 59, 61, 64, 71, 73, 79, 81)


def ordered_profiles():
    result = []
    for c in (4, 6, 8, 9):
        pairs = [(a, b) for b in range(c, 10*c + 8)
                 for a in range(b, (3*c + 4)*b + 3*c + 1)]
        for modulus in PROFILE_MODULI:
            units = [u for u in range(modulus) if gcd(u, modulus) == 1]
            values = [1] * len(units)
            images = [(1,)]
            for e in range(1, max(a for a, b in pairs) + 1):
                values = [(e + 1 + u*f) % modulus for u, f in zip(units, values)]
                images.append(tuple(sorted(set(values))))

            @lru_cache(None)
            def two_products(B):
                return tuple({v*w % modulus for v in B for w in images[c]})

            @lru_cache(None)
            def three_products(A, B):
                return frozenset(u*z % modulus for u in A for z in two_products(B))

            survivors = []
            for a, b in pairs:
                D = (a + 1)*(b + 1)*(c + 1)
                if D <= 2*modulus or (D + 1) % modulus in three_products(images[a], images[b]):
                    survivors.append((a, b))
            two_products.cache_clear()
            three_products.cache_clear()
            pairs = survivors
        ordered = {triple for a, b in pairs for triple in permutations((a, b, c))}
        print("Minimum", c, "profiles", len(pairs), "orders", len(ordered), flush=True)
        result.extend(sorted(ordered))
    return result


def moment(base, e):
    value = 0
    for coefficient in range(e + 1, 0, -1):
        value = base*value + coefficient
    return value


@lru_cache(None)
def normalized_table(modulus, e):
    return tuple(None if gcd(t, modulus) != 1 else
                 moment(t, e)*pow(t, -e, modulus) % modulus for t in range(modulus))


@lru_cache(None)
def permitted_y(i, j, k, x, modulus):
    D = (i + 1)*(j + 1)*(k + 1)
    u = normalized_table(modulus, i)[x]
    last = set(normalized_table(modulus, k)) - {None}
    return tuple(False if v is None else any((u*v*w - D - 1) % modulus == 0 for w in last)
                 for v in normalized_table(modulus, j))


def prime_list(limit):
    table = bytearray(b'\x01')*(limit + 1)
    table[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if table[p]:
            table[p*p::p] = b'\x00'*((limit - p*p)//p + 1)
    return array('I', (t for t, prime in enumerate(table) if prime))


def middle_prime_interval(i, j, k, x):
    D = (i + 1)*(j + 1)*(k + 1)
    H = moment(x, i)
    full = (D + 1)*x**i
    gap = full - (j + 1)*(k + 1)*H
    if gap <= 0:
        return None
    lower = max(x, j*D//(j + 1), j*(k + 1)*H//gap) + 1
    upper = 1 + 2*full//gap
    if lower <= upper:
        return i, j, k, x, H, full, lower, upper
    return None


def check_remaining(rows):
    jobs = [job for row in rows if (job := middle_prime_interval(*row)) is not None]
    ceiling = max(job[-1] for job in jobs)
    primes = prime_list(ceiling)
    examined = local_pairs = divisibility_pairs = local_rows = 0
    for i, j, k, x, H, full, lower, upper in jobs:
        if x <= max(PAIR_MODULI):
            raise ArithmeticError("The local tests need units at every modulus")
        left = bisect_left(primes, lower)
        right = bisect_right(primes, upper)
        examined += right - left
        tests = []
        for modulus in PAIR_MODULI:
            allowed = permitted_y(i, j, k, x % modulus, modulus)
            if not any(allowed):
                break
            tests.append((sum(allowed) / modulus, modulus, allowed))
        if len(tests) != len(PAIR_MODULI):
            continue
        local_rows += 1
        # The floating key affects only the order of Boolean tests.
        tests.sort()
        for index in range(left, right):
            y = primes[index]
            if any(not allowed[y % modulus] for _, modulus, allowed in tests):
                continue
            local_pairs += 1
            W = H*moment(y, j)
            N = full*y**j
            gap = N - (k + 1)*W
            if gap <= 0:
                continue
            z = k*W//gap + 1
            if z <= y or W % z:
                continue
            divisibility_pairs += 1
            if W % z**k == 0 and W*moment(z, k) == N*z**k:
                raise ArithmeticError(("Ordered integer equality", i, j, k, x, y, z))
    print("Prime-x cases", len(rows), "nonempty y ranges", len(jobs), "locally possible x", local_rows)
    print("Largest prime bound", ceiling, "prime pairs", examined, "local survivors", local_pairs,
          "ordered candidates with z dividing W", divisibility_pairs, "equalities", 0)


def main():
    source = Path(__file__).with_suffix('.cpp')
    with TemporaryDirectory() as tmp:
        binary = Path(tmp) / 'intervals'
        profile_file = Path(tmp) / 'profiles.txt'
        row_file = Path(tmp) / 'rows.txt'
        run(['c++', '-std=c++20', '-O3', str(source), '-lgmpxx', '-lgmp', '-o', str(binary)],
            check=True)
        with profile_file.open('w') as stream:
            for triple in ordered_profiles():
                print(*triple, file=stream)
        with profile_file.open() as stream:
            run([str(binary), str(row_file)], stdin=stream, check=True)
        rows = [tuple(map(int, line.split())) for line in row_file.read_text().splitlines()]
        check_remaining(rows)


if __name__ == '__main__':
    main()
