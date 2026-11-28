"""Independent arithmetic and literal checks; these are supplementary to Lean."""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
RULES = {"00": "0101", "10": "001"}
PATTERN = re.compile("00|10")
CODE = {"A": "10", "B": "100", "C": "1000"}
SIGMA = {"A": "B", "B": "C", "C": "AAB"}
TAILS = ["BAA", "CB", "ABA", "BC", "CAA", "ABB", "BCA", "AAB", "BBA", "CC"]
EXTRA = ["", "A", "", "", "A", "", "C", "", "", "AA"]
GAIN = [1, 0, 1, 1, 1, 0, 1, 0, 1, 1]
INITIAL = [2, 4, 5, 7, 9, 12, 17, 23, 33, 48, 70, 103, 152, 228, 343, 515]
COEFF = [2, -1, 2, -4, 4, -4, 4, -4, 4, -3, 2, -3, 2]


def scan(word):
    output = []
    j = 0
    while j < len(word):
        pair = word[j:j + 2]
        if pair in RULES:
            output.append(RULES[pair])
            j += 2
        else:
            output.append(word[j])
            j += 1
    return "".join(output)


def decode(core):
    return "".join(CODE[c] for c in core)


def sigma(core):
    return "".join(SIGMA[c] for c in core)


def left(p):
    return "AC" if p % 2 else ""


def shape(p, core, t):
    return "0" * (3 if p % 2 else 1) + decode(core + TAILS[p]) + "1" * (t + 1)


def advance(state):
    p, a, b, c, t = state
    addition = Counter(left(p) + EXTRA[p])
    return ((p + 1) % 10, 2*c + addition["A"], a+c,
            b + addition["C"], t + GAIN[p])


def observe(state):
    p, a, b, c, t = state
    return 2*a + 3*b + 4*c + t + 1 + (3 if p % 2 else 1) + len(decode(TAILS[p]))


def main():
    lengths = INITIAL[:]
    for n in range(16, 2001):
        lengths.append(sum(c * lengths[n-i-1] for i, c in enumerate(COEFF)))
    word = "00"
    literal = []
    for n in range(34):
        assert len(word) == lengths[n], n
        literal.append(len(word))
        if n < 33:
            manual = scan(word)
            regular = PATTERN.sub(lambda match: RULES[match[0]], word)
            assert manual == regular, n
            word = manual
    boundary_cases = 0
    for k in range(5):
        for letters in product("ABC", repeat=k):
            core = "".join(letters)
            for p in range(10):
                for t in [0, 1, 7]:
                    assert scan(shape(p, core, t)) == shape(
                        (p+1) % 10, left(p) + sigma(core) + EXTRA[p], t + GAIN[p])
                    boundary_cases += 1
    state = (0, 3, 4, 4, 5)
    for n in range(9, 2001):
        assert observe(state) == lengths[n], n
        state = advance(state)
    # For each phase the 13-step defect is affine in four coordinates.
    # Evaluating the zero vector and four unit vectors checks all coefficients.
    certificate_cases = 0
    for p in range(10):
        for basis in [(0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0),
                      (0, 0, 1, 0), (0, 0, 0, 1)]:
            state = (p,) + basis
            values = []
            for _ in range(14):
                values.append(observe(state))
                state = advance(state)
            assert values[13] == sum(c * values[12-i] for i, c in enumerate(COEFF))
            certificate_cases += 1
    report = {
        "literal_manual_and_regex": "agree through index 33",
        "literal_lengths": literal,
        "boundary_cases": boundary_cases,
        "state_and_independent_recurrence": "agree through index 2000",
        "affine_certificate_basis_cases": certificate_cases,
        "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted((HERE / "sources").glob("*.seq"))},
        "scope": "Supplementary finite checks; all-index correctness is proved in Lean.",
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
