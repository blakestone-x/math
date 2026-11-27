"""Produce the full induction certificate and independently check small words."""

from collections import deque


def step(state, p, q, bit):
    c, m = state
    v, w = c + p * bit, m ^ (q * bit)
    return None if (v ^ w) & 1 else (v // 2, w // 2)


def certificate():
    start = ((0, 0), (0, 0))
    queue = deque([start])
    ids = {start: 0}
    rows = []
    while queue:
        state = queue.popleft()
        left, right = state
        if left[0] == left[1] and right[0] != right[1]:
            raise AssertionError(("terminal contradiction", state))
        successors = []
        for bit in range(2):
            a = step(left, 15, 23, bit)
            if a is None:
                successors.append("–")
                continue
            b = step(right, 13, 21, bit)
            if b is None:
                raise AssertionError(("right side rejected", state, bit))
            pair = (a, b)
            if pair not in ids:
                ids[pair] = len(ids)
                queue.append(pair)
            successors.append(str(ids[pair]))
        rows.append((ids[state], left, right, *successors))
    return rows


def small_check(bits=15):
    limit = 1 << bits
    image = {x | (x << 2) for x in range(limit)}
    differences = []
    for n in range(limit):
        a = (15 * n == (n ^ (n << 1) ^ (n << 2) ^ (n << 4)))
        b = (13 * n == (n ^ (n << 2) ^ (n << 4)))
        c = n in image
        b_direct = True
        c_direct = True
        for i in range(bits):
            mid = (n >> i) & 1
            left = ((n << 2) >> i) & 1
            right = (n >> (i + 2)) & 1
            if left == right and left != mid:
                b_direct = False
            if not left and mid and not right:
                c_direct = False
        if b_direct != b or c_direct != c or a > b or b > c:
            raise AssertionError(n)
        if c and not b:
            differences.append(n)
    if differences[0] != 325:
        raise AssertionError(differences[0])


if __name__ == "__main__":
    for i, a, b, z, o in certificate():
        print(f"| {i} | {a} | {b} | {z} | {o} |")
    small_check()
