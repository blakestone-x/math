"""Construct XOR/AND straight-line programs and check the gate bound."""

from math import comb


def circuit(n, k):
    if not 1 <= k <= n:
        raise ValueError("require 1 <= k <= n")
    gates = []

    def gate(op, x, y):
        gates.append((op, x, y))
        return n + len(gates) - 1

    def parity(wires):
        value = wires[0]
        for bit in wires[1:]:
            value = gate("xor", value, bit)
        return value

    def elementary(wires, degree):
        if degree == 1:
            return parity(wires)
        odd = degree % 2
        residual = wires[:-1] if odd else list(wires)
        carries = []
        while len(residual) >= 3:
            x, y, z = residual.pop(), residual.pop(), residual.pop()
            xy = gate("xor", x, y)
            xz = gate("xor", x, z)
            carries.append(gate("xor", x, gate("and", xy, xz)))
            residual.append(gate("xor", xy, z))
        if len(residual) == 2:
            carries.append(gate("and", *residual))
        result = elementary(carries, degree // 2)
        return gate("and", result, parity(wires)) if odd else result

    out = elementary(list(range(n)), k)
    return gates, out


def bound(n, k):
    return k - 1 + sum((n - k) >> j for j in range(1, k.bit_length()))


def eval_words(gates, output, inputs):
    values = list(inputs)
    for op, x, y in gates:
        values.append(values[x] & values[y] if op == "and" else values[x] ^ values[y])
    return values[output]


if __name__ == "__main__":
    for n in range(1, 101):
        for k in range(1, n + 1):
            gates, out = circuit(n, k)
            used = sum(op == "and" for op, _, _ in gates)
            if used != bound(n, k):
                raise AssertionError((n, k, used))
    for n in range(1, 13):
        size = 1 << n
        inputs = [sum(((x >> i) & 1) << x for x in range(size)) for i in range(n)]
        for k in range(1, n + 1):
            want = sum((comb(x.bit_count(), k) % 2) << x for x in range(size))
            gates, out = circuit(n, k)
            if eval_words(gates, out, inputs) != want:
                raise AssertionError((n, k))
    print("Checked 5050 gate counts for n <= 100 and every truth table for n <= 12.")
