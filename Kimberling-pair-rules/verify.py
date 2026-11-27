"""Independent literal scanner and gap construction for Kimberling's two rules."""
import re
from fractions import Fraction


def scan(word, one):
    return re.sub(b"00|1", lambda token: b"001" if token[0] == b"00" else one, word)


def tiles(gaps):
    return b"".join(b"1" + b"0" * gap for gap in gaps)


def limit_prefix(length, start, sub):
    body = bytearray(b"00")
    power = [start]
    while len(body) < length:
        body.extend(tiles(power))
        power = [new for old in power for new in sub[old]]
    return bytes(body[:length])


def check(one, h, sub, tails, extras, upto=23):
    pad = b"0" * h
    for k, image in sub.items():
        assert scan(tiles([k]), one) + pad == pad + tiles(image)
    for j, suffix in enumerate(tails):
        assert scan(suffix, one) == pad + tiles(extras[j]) + tails[(j + 1) % len(tails)]
    lengths = []
    w = b"00"
    for n in range(upto + 1):
        lengths.append(len(w))
        if one == b"010" and n >= 3:
            assert lengths[n] == sum(lengths[n - 3:n])
        if one == b"000" and n >= 7:
            L = lengths
            assert L[n] == L[n-1] + 2*L[n-2] - L[n-3] - L[n-4] + 2*L[n-5] - 2*L[n-7]
        if n < upto:
            new = scan(w, one)
            assert new.startswith(w)
            w = new
    assert limit_prefix(len(w), h, sub) == w
    p = q = 0
    for position, bit in enumerate(w, 1):
        if bit == ord("1"):
            p += 1
            if one == b"010":
                assert 5*p <= 2*position and position <= 4*p
            elif p == 1:
                assert position == 3
            else:
                assert 4*p <= position < 6*p
        else:
            q += 1
            assert q <= position <= 2*q
    if one == b"010":
        assert lengths[:7] == [2, 3, 6, 11, 20, 37, 68]
    else:
        assert lengths[:8] == [2, 3, 6, 10, 17, 29, 51, 90]
    print(f"1 -> {one.decode()}: literal lengths through n={upto}; {len(w)} binary letters, {p} one-positions, {q} zero-positions.")


def root_bounds():
    for lo, hi, cubic, numerator, denominator, low_m, high_m in [
        (18392,18393,lambda x: x**3-x*x-x-1,lambda x: 2+3*x+4*x*x,
         lambda x: 1+x+x*x,3,Fraction(7,2)),
        (17692,17693,lambda x: x**3-2*x-2,lambda x: 3*x*x+6*x+4,
         lambda x: x*x+x,4,5),
    ]:
        a, b = Fraction(lo, 10000), Fraction(hi, 10000)
        assert cubic(a) < 0 < cubic(b)
        assert low_m < numerator(a) / denominator(b) <= numerator(b) / denominator(a) < high_m


if __name__ == "__main__":
    root_bounds()
    check(b"010", 1, {1:[3], 2:[3,1], 3:[3,2]},
          [tiles([i]) for i in (0,1,2)], [[],[],[3]])
    check(b"000", 5, {2:[5], 5:[2,6], 6:[2,2,5]},
          [tiles(w) for w in [(5,2,5),(5,2,1),(2,6,4),(5,2,0),(2,6,3),(2,5,1)]],
          [[2,6],[],[5,2,2],[],[5,2],[]])
