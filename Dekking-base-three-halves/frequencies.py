"""Exact factor frequencies in the two base-3/2 words. Positions start at zero."""
from fractions import Fraction
from functools import cache


def _parent_word(word, phase, sibling):
    """Decode constraints on consecutive parent bits, or return None on a conflict."""
    out = []
    previous = -1
    for j, symbol in enumerate(word, phase):
        if sibling:
            parent, flip = j // 3, j % 3 == 1
        else:
            parent, flip = 2 * j // 3, j % 3 == 2
        value = str(int(symbol) ^ flip)
        if parent == previous:
            if out[-1] != value:
                return None
        else:
            out.append(value)
            previous = parent
    return ''.join(out)


@cache
def _t(word):
    if word is None:
        return Fraction(0)
    length = len(word)
    if length == 0:
        return Fraction(1)
    if length == 1:
        return Fraction(1, 2)
    if length == 2:
        return Fraction(3, 10) if word[0] == word[1] else Fraction(1, 5)
    if length == 3:
        return Fraction(1, 20) if word in ('010', '101') else Fraction(3, 20)
    return sum((_t(_parent_word(word, r, False)) for r in range(3)), Fraction(0)) / 3


def frequency(word, sibling=True):
    """Return an exact Fraction for Dekking's A357448 or, with sibling=False, t."""
    if any(b not in '01' for b in word):
        raise ValueError('a word must contain only 0 and 1')
    if not sibling:
        return _t(word)
    return sum((_t(_parent_word(word, r, True)) for r in range(3)), Fraction(0)) / 3


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('word', type=str, help='binary word')
    parser.add_argument('--normalized', action='store_true', help='use the normalized word t')
    args = parser.parse_args()
    print(frequency(args.word, sibling=not args.normalized))
