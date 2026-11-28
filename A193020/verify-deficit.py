"""Enumerate smallest schedules and test the two collision bounds exactly."""
from itertools import combinations, groupby, product
from math import comb


def schedules(n):
    # Choosing the positions of A in lexicographic order gives the smallest
    # schedule for each output first (A < B).
    for positions in combinations(range(2*n), n):
        source = [1]*(2*n)
        for i in positions:
            source[i] = 0
        yield tuple(source)


def check_word(word, choices):
    n = len(word)
    runs = [len(list(g)) for _, g in groupby(word)]
    marked = []
    for i in range(n-1):
        if word[i] != word[i+1] and (not marked or i >= marked[-1]+3):
            marked.append(i)
    assert 3*len(marked) >= len(runs)-1

    seen = set()
    by_first = [0, 0]
    for schedule in choices:
        heads = [0, 0]
        output = []
        for stream in schedule:
            output.append(word[heads[stream]])
            heads[stream] += 1
        output = tuple(output)
        if output in seen:
            continue
        seen.add(output)
        by_first[1-schedule[-1]] += 1
        assert all(not (schedule[i:i+2] == (1, 0) and output[i] == output[i+1])
                   for i in range(2*n-1))

    for count in by_first:
        assert count*8**len(marked) <= 4**n*7**len(marked)
    a = 0
    for length in runs:
        time = 2*a+length
        block = length//4
        bad = sum(comb(time, k) for k in range(time+1) if 2*abs(2*k-time) > length)
        assert len(seen) <= bad*2**(2*n-time)+(block+1)*2**(2*n-block)
        a += length
    return len(seen)


def main():
    maxima = []
    for n in range(1, 8):
        choices = list(schedules(n))
        maxima.append(max(check_word(word, choices) for word in product((0, 1), repeat=n)))
    assert maxima == [1, 2, 4, 9, 18, 54, 120]
    print("All binary inputs through length 7 passed. Exact maxima:", maxima)


if __name__ == "__main__":
    main()
