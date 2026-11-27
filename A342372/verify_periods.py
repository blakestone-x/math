"""Construct attack equations and check their integer torsion or ordinary-board vertex."""

from math import gcd, lcm, prod

from partitions import diagonal_factors


class Equations:
    def __init__(self, pieces):
        self.width = 2*pieces
        self.matrix = []
        self.rhs = []

    def attack(self, i, j, direction):
        assert i != j
        weights = {'row': (1, 0), 'column': (0, 1), 'sum': (1, 1), 'difference': (1, -1)}
        form = [0] * self.width
        for s, weight in enumerate(weights[direction]):
            form[2*i+s], form[2*j+s] = weight, -weight
        self.matrix.append(form)
        self.rhs.append(0)

    def pin(self, label, coordinate, value):
        assert value in (0, 1)
        form = [0] * self.width
        form[2*label+coordinate] = 1
        self.matrix.append(form)
        self.rhs.append(value)

    def check_vertex(self, scaled, denominator):
        assert self.width == len(scaled) == len(self.matrix)
        assert gcd(denominator, *scaled) == 1
        assert all(0 <= value <= denominator for value in scaled)
        assert all(sum(a*b for a, b in zip(row, scaled)) == denominator*target
                   for row, target in zip(self.matrix, self.rhs))
        assert len(diagonal_factors([row.copy() for row in self.matrix])) == self.width


def binary_chain(a):
    values, parents = [1], []
    for bit in bin(a)[3:]:
        last = len(values)-1
        parents.append((last, last))
        values.append(2*values[last])
        if bit == '1':
            parents.append((last+1, 0))
            values.append(values[-1]+1)
    assert values[-1] == a
    return values, parents


def addition_chain_check(a, padding, ordinary=False):
    values, parents = binary_chain(a)
    steps = len(parents)
    used = 1 + 3*steps + int(ordinary)
    pieces = used + padding
    system = Equations(pieces)
    scaled = [0] * (2*pieces)
    row_axes = [1+2*i for i in range(steps)]
    col_axes = [2+2*i for i in range(steps)]
    for i, (row_axis, col_axis) in enumerate(zip(row_axes, col_axes)):
        system.attack(row_axis, 0, 'column')
        system.attack(col_axis, 0, 'row')
        system.attack(row_axis, col_axis, 'sum')
        scaled[2*row_axis] = scaled[2*col_axis+1] = values[i]
    if ordinary:
        final_anchor = 1+3*steps
        scaled[2*final_anchor+1] = a
        for coordinate in (0, 1):
            system.pin(0, coordinate, 0)
            system.pin(final_anchor, coordinate, coordinate)
        for label in range(used, pieces):
            for coordinate in (0, 1):
                system.pin(label, coordinate, 0)
    else:
        final_anchor = 0
    for i, (u, v) in enumerate(parents, start=1):
        gate = 2*steps+i
        system.attack(gate, row_axes[u], 'row')
        system.attack(gate, col_axes[v], 'column')
        system.attack(gate, row_axes[i] if i < steps else final_anchor, 'sum')
        scaled[2*gate], scaled[2*gate+1] = values[u], values[v]
    if ordinary:
        system.check_vertex(scaled, a)
    else:
        factors = diagonal_factors([row.copy() for row in system.matrix])
        assert 2*pieces-len(factors) == 2+2*padding
        assert prod(factors) == lcm(*factors) == a


def ordinary_queen_check(a, steps, padding):
    if steps == 0:
        assert a == 1
        return
    bits = f'{(1 << steps)-a:0{steps}b}'
    assert len(bits) == steps
    pieces = 1 + 2*steps + padding
    system = Equations(pieces)
    scaled = [0]*(2*pieces)
    system.pin(0, 0, 0)
    system.pin(0, 1, 0)
    numerator = 1
    for i, b in enumerate(bits):
        p, q = 1+2*i, 2+2*i
        scaled[2*p:2*p+2] = [numerator, numerator]
        numerator = 2*numerator-int(b)
        scaled[2*q:2*q+2] = [numerator, int(b)]
        system.attack(p, 0, 'difference')
        system.attack(q, 1 if b == '1' else 0, 'column')
        system.attack(q, p, 'sum')
        if i+1 < steps:
            system.attack(q, p+2, 'row')
        else:
            system.pin(q, 0, 1)
    for label in range(1+2*steps, pieces):
        system.pin(label, 0, 0)
        system.pin(label, 1, 0)
    assert numerator == a
    system.check_vertex(scaled, a)


if __name__ == '__main__':
    for a in range(2, 65):
        for padding in (0, 2):
            addition_chain_check(a, padding)
            addition_chain_check(a, padding, ordinary=True)
    for steps in range(7):
        for a in range(1, (1 << steps)+1):
            for padding in (0, 2):
                ordinary_queen_check(a, steps, padding)
    print('Verified integral translation presentations and ordinary semiqueen vertices for denominators 2–64.')
    print('Verified every ordinary queen vertex in all binary constructions of length up to six, with and without padding.')
