"""Reproduce the example residues and onset indices in the proof note.

These finite calculations illustrate the theorem. The universal proof is in
Proof.lean; the argument does not depend on this program or its output.
Indices here follow OEIS: the two supplied seeds have indices 1 and 2.
"""


def terms(first: int, second: int, count: int = 100) -> list[int]:
    values = [0, first, second]  # index zero is unused
    while len(values) <= count:
        total = values[-2] + values[-1]
        values.append(total // 2 if total % 2 == 0 else 3 * total + 1)
    return values


def stable_residue(k: int) -> int:
    return ((2**k % 5) * 3**k) // 5


def first_certifying_pair(values: list[int], k: int) -> int:
    modulus = 3**k
    residue = stable_residue(k)
    for n in range(1, len(values) - 1):
        if values[n] % modulus == residue == values[n + 1] % modulus:
            return n
    raise ValueError("Increase the number of generated terms")


def main() -> None:
    first = terms(1, 2)
    second = terms(0, 1)
    print("OEIS indexing: initial terms have indices 1 and 2.")
    print("N is the first pair of adjacent terms in the target residue class.")
    print("The proved persistence lemma makes the entire tail from N stable.")
    print()
    print(" k    3^k   residue    N(A105801)    N(A181717)")
    for k in range(1, 13):
        print(
            f"{k:2d} {3**k:6d} {stable_residue(k):9d}"
            f" {first_certifying_pair(first, k):13d}"
            f" {first_certifying_pair(second, k):13d}"
        )


if __name__ == "__main__":
    main()
