"""Independent checks of modular Ducci preperiods using only integer operations."""

from itertools import product


def prime_powers(m):
    p = 2
    while p * p <= m:
        exponent = 0
        while m % p == 0:
            exponent += 1
            m //= p
        if exponent:
            yield p, exponent
        p += 1
    if m > 1:
        yield m, 1


def prediction(m, n):
    factors = dict(prime_powers(m))
    if n % 2:
        return factors.get(2, 0)
    local_indices = []
    for p, exponent in factors.items():
        reduced = n
        while reduced % p == 0:
            reduced //= p
        prime_part = n // reduced
        if prime_part == 1:
            local_indices.append(1)
        else:
            local_indices.append((prime_part // p) * (exponent * (p - 1) + 1))
    return max(local_indices)


def step(state, m):
    return tuple((x + y) % m for x, y in zip(state, state[1:] + state[:1]))


def unit_seed_preperiod(m, n):
    state = (1,) + (0,) * (n - 1)
    times = {}
    while state not in times:
        times[state] = len(times)
        state = step(state, m)
    return times[state]


def periodic_by_congruences(m, state):
    n = len(state)
    if n % 2:
        return sum(state) % (m & -m) == 0
    for p, exponent in prime_powers(m):
        reduced = n
        while reduced % p == 0:
            reduced //= p
        prime_part = n // reduced
        alternating_sums = [0] * prime_part
        for j, value in enumerate(state):
            alternating_sums[j % prime_part] += -value if j % 2 else value
        if any(total % p**exponent for total in alternating_sums):
            return False
    return True


def maximum_over_all_seeds(m, n):
    # Repeatedly take the image of the entire configuration space until it
    # consists only of cycles. The number of strict inclusions is the longest tail.
    states = set(product(range(m), repeat=n))
    steps = 0
    while True:
        image = {step(state, m) for state in states}
        if len(image) == len(states):
            predicted = {state for state in product(range(m), repeat=n) if periodic_by_congruences(m, state)}
            assert image == predicted, (m, n, "periodic tuples")
            return steps
        steps += 1
        states = image


def main():
    unit_cases = set(product(range(2, 13), range(1, 9)))
    unit_cases.update(((9, 6), (25, 10), (72, 12), (27, 18), (16, 12), (9, 18)))
    for m, n in sorted(unit_cases):
        actual = unit_seed_preperiod(m, n)
        assert actual == prediction(m, n), (m, n, actual)
    print(f"Direct unit-seed orbit: {len(unit_cases)} modulus-width pairs passed.")

    graph_count = 0
    states_tested = 0
    for m in range(2, 11):
        for n in range(1, 9):
            if m**n > 30000:
                continue
            actual = maximum_over_all_seeds(m, n)
            assert actual == prediction(m, n), (m, n, actual)
            graph_count += 1
            states_tested += m**n
    print(f"Complete configuration spaces: {graph_count} pairs, {states_tested} states.")

    boundary_cases = 0
    for p in (2, 3, 5, 7, 11):
        for k in range(1, 5):
            size = p**k
            if size > 400:
                continue
            for exponent in range(1, 7):
                modulus = p**exponent
                index = (size // p) * (exponent * (p - 1) + 1)
                state = (1,) + (0,) * (size - 1)
                for time in range(index):
                    assert any(state), (p, k, exponent, time)
                    state = tuple((x - y) % modulus for x, y in zip(state, state[-1:] + state[:-1]))
                assert not any(state), (p, k, exponent, index)
                boundary_cases += 1
    print(f"Cyclic finite differences: {boundary_cases} exact nilpotency indices passed.")


if __name__ == "__main__":
    main()
