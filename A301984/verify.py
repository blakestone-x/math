"""Compare the theorem with direct subsequence matching over a finite prefix."""

from itertools import count


def is_subsequence(target, host):
    position = 0
    for bit in target:
        index = host.find(bit, position)
        if index == -1:
            return False
        position = index + 1
    return True


def value(n):
    host = format(n, "b")
    for candidate in count(1):
        if not is_subsequence(format(candidate, "b"), host):
            return candidate - 1


def check(limit):
    observed = []
    largest = 0
    for n in range(1, limit + 1):
        current = value(n)
        if current > largest:
            largest = current
            observed.append((n, current))

    predicted = []
    # A subsequence represents an integer no larger than its host.
    for record in range(1, limit + 1):
        bits = format(record, "b")
        if bits.count("0") <= 1:
            index = int(bits.replace("1", "01"), 2)
            if index <= limit:
                predicted.append((index, record))

    if predicted != observed:
        raise AssertionError((predicted, observed))
    print(f"Checked {limit} hosts and {len(observed)} records. Last pair {observed[-1]}.")


if __name__ == "__main__":
    check(10_000)
