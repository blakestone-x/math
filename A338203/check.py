"""Cross-check the signed-state computation with ordinary integer subtraction."""
from pathlib import Path


def reverse(word, width):
    return int(f'{word:0{width}b}'[::-1], 2)


def hit(word, width):
    seen = set()
    while (r := reverse(word, width)) != word:
        if word in seen:
            raise ArithmeticError(f'cycle starting at {word} in width {width}')
        seen.add(word)
        word = (word - r) % (1 << width)
    return len(seen)


def delete_middle(word, pairs):
    return ((word >> (pairs + 1)) << pairs) | (word % (1 << pairs))


def all_times(width):
    # Each new path stops at an already measured state or an initial palindrome.
    times = [-1] * (1 << width)
    for start in range(len(times)):
        word = start
        path = []
        while times[word] == -1:
            reflected = reverse(word, width)
            if reflected == word:
                times[word] = 0
                break
            times[word] = -2
            path.append(word)
            word = (word - reflected) % len(times)
        if times[word] < 0:
            raise ArithmeticError(f'cycle in width {width}')
        distance = times[word]
        for word in reversed(path):
            distance += 1
            times[word] = distance
    return times


def main():
    rows = Path(__file__).with_name('maxima.txt').read_text().splitlines()
    records = [tuple(map(int, row.split())) for row in rows[1:]]
    previous = [0]
    for width in range(1, 18):
        times = all_times(width)
        if width % 2:
            if any(t != previous[delete_middle(w, width // 2)] for w, t in enumerate(times)):
                raise ArithmeticError(f'central deletion failed at width {width}')
        elif max(times) != records[width // 2 - 1][2]:
            raise ArithmeticError(f'direct maximum differs at width {width}')
        previous = times
    known = [2, 5, 7, 14, 16, 18, 27, 31, 33, 41, 46, 50, 57, 61, 70]
    if [row[2] for row in records[:15]] != known:
        raise ArithmeticError('disagreement with the initial OEIS table')
    if len(records) != 20:
        raise ArithmeticError('expected results for 1 through 20 pairs')
    for i, (m, states, maximum, witness) in enumerate(records, 1):
        if m != i or states != 3**m or hit(witness, 2*m) != maximum:
            raise ArithmeticError(f'invalid maximum witness for {m} pairs')
    print('All words checked at widths 1..17. The first 15 tabulated maxima and all 20 witnesses agree.')


if __name__ == '__main__':
    main()
