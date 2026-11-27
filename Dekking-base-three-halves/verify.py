"""Independent finite checks of the manuscript's exact formulas."""
from collections import Counter
from fractions import Fraction
from itertools import product

from frequencies import _parent_word, frequency


def expand(bits, sibling):
    if sibling:
        return ''.join(a + str(1-int(a)) + a for a in bits)
    return ''.join(a + a + str(1-int(b)) for a, b in zip(bits[::2], bits[1::2]))


def words(length):
    return (''.join(x) for x in product('01', repeat=length))


def check_literal_decoding():
    checked = 0
    for m in range(1, 11):
        for sibling in (False, True):
            for r in range(3):
                size = ((r + m + 2) // 3) * (1 if sibling else 2)
                offset = 0 if sibling else 2*r//3
                # Recover the full inverse image by enumerating all possible parent strings.
                inverse = {}
                for v in words(size):
                    w = expand(v, sibling)[r:r+m]
                    inverse.setdefault(w, set()).add(v)
                for w in words(m):
                    d = _parent_word(w, r, sibling)
                    if d is None:
                        assert w not in inverse
                    else:
                        expected = {a+d+b for a in words(offset)
                                    for b in words(size-offset-len(d))}
                        assert inverse[w] == expected
                    checked += 1
    print(f'Literal inverse-image checks: {checked} cylinder/phase/word combinations.')


def check_probabilities(max_length=13):
    checked = 0
    for m in range(max_length+1):
        for sibling in (False, True):
            table = {w: frequency(w, sibling) for w in words(m)}
            assert sum(table.values()) == 1
            for w, f in table.items():
                assert f >= 0
                assert f == table[w[::-1]] == table[w.translate(str.maketrans('01','10'))]
                if m < max_length:
                    assert f == frequency(w+'0',sibling) + frequency(w+'1',sibling)
                    assert f == frequency('0'+w,sibling) + frequency('1'+w,sibling)
                if m >= 2 or sibling:
                    assert 3*f == sum(frequency(v,False) for r in range(3)
                                      if (v := _parent_word(w,r,sibling)) is not None)
                checked += 1
    print(f'Exact mass, symmetry, marginal and transfer checks through length {max_length}: {checked} word/sequence cases.')
    for block in ('010', '101'):
        assert frequency(block*5) == Fraction(1,180)
        assert frequency(block*5+'0') + frequency(block*5+'1') == Fraction(1,180)
        assert frequency(block*6) == 0
    assert [frequency(w) for w in words(2)] == [Fraction(1,10),Fraction(2,5),
                                                 Fraction(2,5),Fraction(1,10)]


def compare_prefixes(N=1_000_000):
    # Generate both words directly from their own 2-to-3 rules.
    t = bytearray(N)
    x = bytearray(N)
    for i in range(1, N):
        k, r = divmod(i,3)
        t[i] = t[2*k] if r < 2 else 1-t[2*k+1]
        x[i] = x[2*k] ^ (r == 1)
    assert all(x[i] == (t[i//3] ^ (i%3 == 1)) for i in range(N))
    assert x[18:33] == bytes((1,0,1))*5 and x[261:276] == bytes((0,1,0))*5
    for u, sibling in ((t,False),(x,True)):
        counts = Counter((u[i],u[i+1]) for i in range(N-1))
        print(f'{"x" if sibling else "t"}: {N} literal bits, pair counts {list(counts[p] for p in product(range(2),repeat=2))}.')
        # A period longer than 64 is covered by the proof. This check compares all starts for the first 64.
        for p in range(1,65):
            longest = run = 0
            for a,b in zip(u,u[p:]):
                run = run+1 if a==b else 0
                if run>longest:
                    longest=run
            assert longest+p <= 5*p
            if longest+p == 5*p:
                assert p == (3 if sibling else 1)


if __name__ == '__main__':
    check_literal_decoding()
    check_probabilities()
    compare_prefixes()
