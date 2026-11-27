"""Check the fixed-point count directly against the base-digit swap criterion."""


def fixed(n):
    width = 1
    while width < n.bit_length():
        blocks = set()
        value = n
        mask = (1 << width) - 1
        while value:
            digit = value & mask
            if digit:
                blocks.add(digit)
            value >>= width
        if len(blocks) == 2:
            return False
        width *= 2
    return True


if __name__ == "__main__":
    for k in range(17):
        actual = sum(fixed(n) for n in range(1 << k, 2 << k))
        expected = 1 << k.bit_count()
        if actual != expected:
            raise AssertionError((k, actual, expected))
    print("Verified every positive integer below 2^17.")
