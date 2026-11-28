"""Compare the search to direct factorization on shifted equations with real solutions."""
import subprocess
import sys

def encode(n):
    remaining, p = n, 2
    digits = []
    while p * p <= remaining:
        exponent = 0
        while remaining % p == 0:
            remaining //= p
            exponent += 1
        if exponent:
            digits.extend((str(p), str(exponent)))
        p += 1
    if remaining > 1:
        digits.extend((str(remaining), '1'))
    return int(''.join(digits))

limit = 100_000
offsets = (0, 7, 38, 7184)
expected = {offset: [] for offset in offsets}
for n in range(2, limit + 1):
    difference = n - encode(n)
    if difference in expected:
        expected[difference].append(n)

assert 32 in expected[7] and 64 in expected[38] and 10935 in expected[7184]
for offset in offsets:
    output = subprocess.check_output([sys.argv[1], str(limit), str(offset)], text=True)
    matches = [int(line.split()[1]) for line in output.splitlines() if line.startswith('match ')]
    assert matches == expected[offset], (offset, matches, expected[offset])
    print(f'offset {offset}: matched direct factorization through {limit}, solutions {matches}')
