#!/usr/bin/env python3
"""Small examples from the original ordered-pair definition; not a proof."""

def count(modulus):
    return sum((x**3 + y**3 - 1) % modulus == 0
               for x in range(modulus) for y in range(modulus))

if __name__ == "__main__":
    print("exponent modulus ordered_pair_count")
    for exponent in range(1, 6):
        modulus = 3**exponent
        value = count(modulus)
        print(exponent, modulus, value)
        assert value == (3 if exponent == 1 else 2*modulus)
