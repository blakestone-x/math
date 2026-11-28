"""Exact finite certificate for all A228456 residues modulo eight. Python 3."""
from collections import defaultdict
from math import comb

MODULUS = 8


def reduce_terms(terms):
    return {k: v % MODULUS for k, v in terms.items() if v % MODULUS}


def multiply(P, Q):
    product = defaultdict(int)
    for (x, y, t), a in P.items():
        for (u, v, w), b in Q.items():
            product[x + u, y + v, t + w] += a * b
    return reduce_terms(product)


def take_digit(P, fourth_power, digit, fold=True):
    # Cartier projects onto terms with exponents congruent to (0,0,digit).
    result = defaultdict(int)
    for (x, y, t), a in P.items():
        for (u, v, w), b in fourth_power.items():
            i, j, k = x + u, y + v, t + w - digit
            if i % 2 or j % 2 or k % 2:
                continue
            i, j, k = i // 2, j // 2, k // 2
            if fold:
                i, j = abs(i), abs(j)
            result[i, j, k] += a * b
    return reduce_terms(result)


def enumerate_states(initial, transition, key):
    states = [initial]
    indices = {key(initial): 0}
    transitions = []
    for state in states:
        pair = []
        for digit in (0, 1):
            child = transition(state, digit)
            k = key(child)
            if k not in indices:
                indices[k] = len(states)
                states.append(child)
            pair.append(indices[k])
        transitions.append(tuple(pair))
    return states, transitions


def ratio_automaton(fold=True):
    Q = {(0, 0, 0): 1, (0, 0, 2): 1}
    directions = ((2, 0), (-2, 0), (1, 1), (1, -1), (-1, 1), (-1, -1))
    for x, y in directions:
        Q[x, y, 1] = -1
    square = multiply(Q, Q)
    fourth = multiply(square, square)
    numerator = multiply({(0, 0, 0): 1, (2, 0, 0): -1}, multiply(Q, square))

    def transition(P, digit):
        return take_digit(P, fourth, digit, fold)

    # The initial low digit 0 extracts the coefficient at t^(2n).
    initial = transition(numerator, 0)
    states, edges = enumerate_states(initial, transition, lambda P: tuple(sorted(P.items())))
    return edges, [P.get((0, 0, 0), 0) for P in states]


def product_automaton(edges, outputs):
    assert all(value % 2 for value in outputs)

    def substitute(mask, digit):
        child_mask = 0
        for i, pair in enumerate(edges):
            if (mask >> i) & 1:
                child_mask ^= 1 << pair[digit]
        return child_mask

    def transition(state, digit):
        prefix, terminal = state
        evens = substitute(prefix, 0)
        return (evens ^ substitute(prefix, 1),
                substitute(terminal, digit) ^ (evens if digit else 0))

    states, transitions = enumerate_states((1, 1), transition, lambda pair: pair)
    results = []
    for _, terminal in states:
        value = 1
        for i, unit in enumerate(outputs):
            if (terminal >> i) & 1:
                value = value * unit % MODULUS
        results.append(value)
    return transitions, results


def minimize(edges, outputs):
    classes = outputs[:]
    while True:
        groups = {}
        labels = [groups.setdefault((outputs[i], classes[a], classes[b]), len(groups))
                  for i, (a, b) in enumerate(edges)]
        if labels == classes:
            break
        classes = labels
    reps = [classes.index(i) for i in range(max(classes) + 1)]
    return [(classes[edges[i][0]], classes[edges[i][1]], outputs[i]) for i in reps]


def direct_check(transitions, maximum=65):
    moments = [sum(comb(n, j)**2 * (comb(2*j, j) // (j + 1)) for j in range(n + 1)) % 8
               for n in range(2*maximum + 1)]
    rows = [[moments[i + j] for j in range(maximum + 1)] for i in range(maximum + 1)]
    determinant = 1
    for i in range(maximum + 1):
        pivot = rows[i][i]
        assert pivot % 2 == 1
        determinant = determinant * pivot % 8
        n, state = i, 0
        while n:
            state = transitions[state][n % 2]
            n //= 2
        assert transitions[state][2] == determinant
        # The inverse of every odd residue modulo eight is itself.
        for j in range(i+1, maximum+1):
            scale = (rows[j][i] * pivot) % 8
            for k in range(i+1, maximum+1):
                rows[j][k] = (rows[j][k] - scale*rows[i][k]) % 8


def main():
    previous = None
    for fold in (True, False):
        edges, ratios = ratio_automaton(fold)
        transitions, outputs = product_automaton(edges, ratios)
        table = minimize(transitions, outputs)
        assert set(outputs) == {1, 3, 5}
        if previous is not None:
            assert table == previous
        previous = table
        print(f"Reflection folding {fold}: {len(edges)} ratio states, "
              f"{len(outputs)} product states, {len(table)} minimal states.")
    print("state | digit 0 | digit 1 | output")
    for i, (a, b, output) in enumerate(table):
        print(f"{i:>5} | {a:>7} | {b:>7} | {output:>6}")
    direct_check(table)
    print("All reachable outputs are 1, 3 or 5. Direct determinants through n=65 agree.")


if __name__ == '__main__':
    main()
