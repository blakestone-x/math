"""Independent infinite-background simulator and exact generating-function audit."""
from collections import Counter
from itertools import accumulate, product


def evolution(rule, steps):
    background, exceptions = 0, {(0, 0)}
    for _ in range(steps + 1):
        yield background, exceptions
        counts = Counter(q for x, y in exceptions
                         for q in ((x+1, y), (x-1, y), (x, y+1), (x, y-1)))
        next_background = (rule >> (9*background)) & 1
        next_exceptions = set()
        for p in exceptions | counts.keys():
            weight = int(p in exceptions) + 2*counts[p]
            index = 9-weight if background else weight
            if ((rule >> index) & 1) != next_background:
                next_exceptions.add(p)
        background, exceptions = next_background, next_exceptions


def cross(n):
    m = n//2
    if n % 2 == 0:
        return ({(0, i) for i in range(-m, m+1)} |
                {(i, 0) for i in range(-m, m+1)} |
                {(i, j) for i in (-1, 1) for j in (-1, 1)})
    strip = {(i, j) for i in (-1, 0, 1) for j in range(-m, m+1)}
    return strip | {(j, i) for i, j in strip} | {(0, m+1), (0, -m-1), (m+1, 0), (-m-1, 0)}


def population(rule, n):
    if n < 5:
        return (1, 5 if rule == 323 else 4, 5, 36, 9)[n]
    return 4*n*n-2*n+6 if n % 2 else 2*n+5


def word(rule, n):
    if rule == 62:
        return ('1', '10')[n] if n < 2 else '0'+'1'*(n//2)+'0'*((n+1)//2)
    if n < 4:
        return ('1', '01', '100', '0011')[n]
    if rule == 73:
        return str(n % 2)*(n+1)
    if n == 4:
        return '10000'
    return '00'+'1'*(n-1) if n % 2 else '11'+'0'*(n-1)


def mask62(x, y, delay):
    if delay < 0:
        return (0,)
    if delay <= 1:
        return (1,)
    if delay <= 3:
        return (int(x*y > 0 and (x+y) % 2 == 0),)
    if abs(x-y) <= 2:
        return (int(x+y > 0 and (x+y) % 2 == 0),)
    return (0, 1)


def stencil(x, y):
    return ((x, y), (x+1, y), (abs(x-1), y), (x, y+1), (x, abs(y-1)))


def rule_bit(rule, center, *neighbors):
    return (rule >> (center+2*sum(neighbors))) & 1


def verify_induction_tables():
    kept = 0
    for h, x, y in product(range(-2, 8), range(8), range(15)):
        if x+y < 3 and h+x+y < 7:
            continue
        target = mask62(x, y, h+1)
        allowed = [mask62(a, b, h+x+y-a-b) for a, b in stencil(x, y)]
        for inputs in product(*allowed):
            assert rule_bit(62, *inputs) in target
        kept += 1
    for rule, m in product((65, 321, 323), range(3, 8)):
        for t in (2*m, 2*m+1):
            source, target = cross(t), cross(t+1)
            for x, y in product(range(12), repeat=2):
                bits = [int(p in source) ^ (t % 2) for p in stencil(x, y)]
                assert rule_bit(rule, *bits) == (((x, y) in target) ^ ((t+1) % 2))
    print(f'Inductive local checks: {kept} rule-62 mask triples with all completions; '
          'two transitions at 720 cross triples for each of three rules.')


def verify_geometry():
    for rule in (62, 65, 73, 321, 323):
        for n, (background, exceptions) in enumerate(evolution(rule, 55)):
            assert all(max(abs(x), abs(y)) <= n for x, y in exceptions)
            if rule in (65, 321, 323):
                assert background == n % 2
                if n >= 5:
                    assert exceptions == cross(n)
                count = (2*n+1)**2-len(exceptions) if background else len(exceptions)
                assert count == population(rule, n)
            if rule == 73 and n >= 4:
                assert background == n % 2 and not exceptions
            if rule == 62 and n >= 7:
                assert not background
                for x in range(n+2):
                    for y in range(x, n+2):
                        h = n-x-y
                        if h < 0:
                            expected = False
                        elif h <= 1:
                            expected = True
                        elif h <= 3:
                            expected = x > 0 and y > 0 and (x+y) % 2 == 0
                        elif y-x <= 2:
                            expected = x+y > 0 and (x+y) % 2 == 0
                        else:
                            continue
                        assert ((x, y) in exceptions) == expected
            if rule in (62, 65, 73):
                observed = ''.join(str(background ^ ((i, i) in exceptions)) for i in range(n+1))
                assert observed == word(rule, n)
    print('Infinite-background simulation: five rules, stages 0 through 55; shapes, counts and diagonals agree.')


# Listed numerator coefficients, in ascending powers of x. Each audit uses the
# denominator in the source entry. Missing degrees have coefficient zero.
published = {
    285612: (1, 0, -1, 0, 10),
    285613: (1, 0, -100, 0, 1000),
    285643: (1, 10, -100, 90, 0, 1000, 10, 0, -1000),
    285644: (1, 1, -1, -90, 0, 100, 100000, 0, -100000),
    285645: (1, 2, -4, 2, 0, 8, 2, 0, -8),
    285646: (1, 1, -1, -2, 0, 4, 32, 0, -32),
    285647: (1, 10, -100, 90, -1, 1011, 100, -1100),
    285648: (1, 1, -1, -90, -10000, 110100, 10000, -110000),
    285649: (1, 2, -4, 2, -1, 11, 4, -12),
    285650: (1, 1, -1, -2, -16, 52, 16, -48),
    269782: (1, 4, 2, 24, -3, 0, 4, 4, -8, 0, 4),
    270084: (1, -3, 22, -16, 32),
    270085: (1, 4, 2, 24, -3, 0, 4, 4, -8, 0, 4),
    270086: (3, 4, 26, -4, -1, 4, 4, -8, 0, 4),
    271254: (1, -2, 15, -2, 24),
    271256: (4, 4, 23, -4, 2, 4, 3, -8, 0, 4),
}


def audit(index, seq, denominator, claimed):
    coefficients = [sum(d*seq[n-i] for i, d in enumerate(denominator) if n >= i)
                    for n in range(len(seq))]
    while coefficients[-1] == 0:
        coefficients.pop()
    expected = published.get(index)
    assert expected is None or tuple(coefficients) == expected, (index, coefficients, expected)
    if claimed is None:
        status = 'no recurrence proposed in entry'
    else:
        failures = [n for n in range(claimed, len(coefficients)) if coefficients[n]]
        status = f'failures in stated range {failures}'
    print(f'A{index}: numerator {coefficients}, recurrence valid from {len(coefficients)}, {status}')


def audit_series():
    horizon = 64
    for index, rule, base, reverse in (
        (285612, 62, 10, True), (285613, 62, 10, False),
        (285643, 65, 10, True), (285644, 65, 10, False),
        (285645, 65, 2, True), (285646, 65, 2, False),
        (285647, 73, 10, True), (285648, 73, 10, False),
        (285649, 73, 2, True), (285650, 73, 2, False),
    ):
        seq = [int(word(rule, n)[::-1] if reverse else word(rule, n), base) for n in range(horizon)]
        if rule == 62:
            c = 1 if reverse else base
            q = (1, -c, -base, c*base)
            claimed = 3
        else:
            q = (1, 0, -1-base**2, 0, base**2)
            claimed = 4 if rule == 65 else 8
        audit(index, seq, q, claimed)
    for rule, (total, dyadic, summed, delta) in (
        (65, (269782, 270084, 270085, 270086)), (323, (270569, 271254, 271255, 271256)),
    ):
        seq = [population(rule, n) for n in range(horizon)]
        sampled = [population(rule, 2**n-1) for n in range(horizon)]
        partial = list(accumulate(seq))
        diff = [b-a for a, b in zip(seq, seq[1:])]
        for n in range(2, horizon):
            assert sampled[n] == 4*4**n-10*2**n+12
        for n in range(4, horizon):
            eps = n % 2
            assert 6*(partial[n]-(rule == 323)) == 4*n**3+12*eps*n*n+35*n-66-3*eps
            if 5 <= n < len(diff):
                assert diff[n] == (-4*n*n+4*n+1 if eps else 4*n*n+4*n+3)
        audit(total, seq, (1, 0, -3, 0, 3, 0, -1), 9 if rule == 65 else None)
        audit(dyadic, sampled, (1, -7, 14, -8), 5)
        audit(summed, partial, (1, -1, -3, 3, 3, -3, -1, 1), 9 if rule == 65 else None)
        audit(delta, diff, (1, 1, -2, -2, 1, 1), 8)


if __name__ == '__main__':
    verify_induction_tables()
    verify_geometry()
    audit_series()
