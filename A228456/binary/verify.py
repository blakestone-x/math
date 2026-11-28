"""Verify the binary formula for OEIS A228456 using Python 3 standard library.

Default: recompute every state in certificate.json, compare it, and check
independent initial determinants. Use --write-certificate to regenerate the JSON.
"""
import argparse
import json
from collections import defaultdict
from math import comb
from pathlib import Path


# Each key consists of the exponents of t, x, y in that order.
Q = {(0, 0, 0): 1, (2, 0, 0): 1}
for exponents in ((2, 0), (-2, 0), (1, 1), (-1, -1), (1, -1), (-1, 1)):
    Q[(1, *exponents)] = -1


def multiply(left, right):
    result = defaultdict(int)
    for (a, b, c), u in left.items():
        for (d, e, f), v in right.items():
            result[a + d, b + e, c + f] += u * v
    return {key: value % 8 for key, value in result.items() if value % 8}


Q2 = multiply(Q, Q)
Q3 = multiply(Q2, Q)
Q4 = multiply(Q3, Q)


def cartier(state, bit):
    result = multiply(dict(state), Q4)
    return tuple(sorted(((a // 2, b // 2, c // 2), v)
                        for (a, b, c), v in result.items()
                        if a % 2 == bit and b % 2 == c % 2 == 0))


def reachable(initial, step):
    states = [initial]
    indices = {initial: 0}
    transitions = []
    for state in states:
        row = []
        for bit in (0, 1):
            child = step(state, bit)
            if child not in indices:
                indices[child] = len(states)
                states.append(child)
            row.append(indices[child])
        transitions.append(row)
    return states, transitions


def set_bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def minimize(transitions, outputs):
    colors = outputs.copy()
    while True:
        patterns = [(colors[i], colors[a], colors[b])
                    for i, (a, b) in enumerate(transitions)]
        palette = {p: i for i, p in enumerate(dict.fromkeys(patterns))}
        refined = [palette[p] for p in patterns]
        if len(set(refined)) == len(set(colors)):
            break
        colors = refined
    quotient = [None] * len(set(colors))
    for i, (a, b) in enumerate(transitions):
        row = [outputs[i], colors[a], colors[b]]
        assert quotient[colors[i]] in (None, row)
        quotient[colors[i]] = row
    return colors, quotient


EXPECTED = [
    [1, 1, 2], [1, 3, 4], [3, 5, 6], [1, 3, 7], [1, 8, 4],
    [3, 5, 5], [1, 6, 6], [5, 9, 4], [1, 3, 10], [5, 11, 7],
    [1, 8, 12], [5, 11, 10], [5, 9, 12],
]


def build_certificate():
    numerator = multiply({(0, 0, 0): 1, (0, 2, 0): -1}, Q3)
    initial = cartier(tuple(numerator.items()), 0)
    states, transitions = reachable(initial, cartier)
    outputs = [dict(state).get((0, 0, 0), 0) for state in states]
    assert len(states) == 33 and all(value % 2 for value in outputs)

    def map_mask(mask, bit):
        image = 0
        for i in set_bits(mask):
            image ^= 1 << transitions[i][bit]
        return image

    def product_transition(state, bit):
        prefix, singles = state
        even = map_mask(prefix, 0)
        odd = map_mask(prefix, 1)
        extra = even if bit else 0
        return even ^ odd, map_mask(singles, bit) ^ extra

    products, product_transitions = reachable((1, 1), product_transition)
    product_outputs = []
    for _, singles in products:
        value = 1
        for i in set_bits(singles):
            value = value * outputs[i] % 8
        product_outputs.append(value)
    assert len(products) == 128
    colors, quotient = minimize(product_transitions, product_outputs)
    assert quotient == EXPECTED
    return {
        'ratio_states': [
            {'terms': [[*key, c] for key, c in state],
             'digits': transitions[i], 'output': outputs[i]}
            for i, state in enumerate(states)],
        'product_states': [
            {'masks': list(state), 'digits': product_transitions[i],
             'output': product_outputs[i], 'class': colors[i]}
            for i, state in enumerate(products)],
        'quotient_output_digit0_digit1': quotient,
    }


def automaton(n):
    state = 0
    while n:
        state = EXPECTED[state][1 + n % 2]
        n //= 2
    return EXPECTED[state][0]


def digit_formula(n):
    if n % 2:
        return 3 if n % 4 == 1 else 1
    m = n // 2
    # A machine tracking (previous two bits, residue sign) has the first
    # digit of m in both memory positions at initialization.
    older = newer = m % 2
    m //= 2
    sign = 0
    while m:
        bit = m % 2
        sign ^= bit * (1 - older)
        older, newer = newer, bit
        m //= 2
    return 1 + 4 * sign


def check_determinants(max_index):
    catalans = [comb(2 * k, k) // (k + 1) for k in range(2 * max_index + 1)]
    h = [sum(comb(n, k)**2 * catalans[k] for k in range(n + 1)) % 8
         for n in range(2 * max_index + 1)]
    gram = [[h[i + j] for j in range(max_index + 1)]
            for i in range(max_index + 1)]
    det = 1
    for i, row in enumerate(gram):
        pivot = row[i]
        assert pivot % 2
        det = det * pivot % 8
        assert det == digit_formula(i), (i, det, digit_formula(i))
        for lower in gram[i + 1:]:
            multiplier = lower[i] * pivot % 8
            for j in range(i + 1, max_index + 1):
                lower[j] = (lower[j] - multiplier * row[j]) % 8


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-certificate', action='store_true')
    parser.add_argument('--direct-through', type=int, default=170)
    args = parser.parse_args()
    path = Path(__file__).with_name('certificate.json')
    cert = build_certificate()
    if args.write_certificate:
        path.write_text(json.dumps(cert, separators=(',', ':')) + '\n')
    else:
        assert json.loads(path.read_text()) == cert
    assert all(digit_formula(i) == automaton(i) for i in range(65536))
    check_determinants(args.direct_through)
    print('33 ratio states, 128 product states and 13 quotient states verified.')
    print('Digit formula matches quotient through n=65535.')
    print(f'Original Hankel determinants checked through n={args.direct_through}.')


if __name__ == '__main__':
    main()
