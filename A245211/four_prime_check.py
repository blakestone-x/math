"""Exhaust the possible fixed points p^a*q*r*s with q < r < s."""
from math import gcd, isqrt


def primes_through(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p::p] = bytes(1 + (limit - p*p) // p)
    return tuple(n for n, yes in enumerate(flags) if yes)


def simple_pairs(b, c):
    """All distinct prime pairs r,s >= 5 with (2r+1)(2s+1)/(rs) = c/b.
    The output can include composite integer candidates, checked by the caller.
    """
    if c <= 4*b or c >= 5*b or b == 1:
        return
    divisor = c*b - 2*b*(2*b+1)
    if divisor > 0:
        other, rem = divmod(b*(2*b+1), divisor)
        if rem == 0:
            yield tuple(sorted((b, other)))
    twice_sum = c - 4*b - 1
    if twice_sum <= 0 or twice_sum % 2:
        return
    total = twice_sum // 2
    disc = total*total - 4*b
    if disc <= 0:
        return
    gap = isqrt(disc)
    if gap*gap == disc and (total - gap) % 2 == 0:
        yield (total-gap)//2, (total+gap)//2


def cases():
    for a in range(1, 23):
        if a % 4 not in (0, 1):
            continue
        C = 8*a + 9
        trial_p = trial_q = positive = hits = prime_hits = 0
        for p in primes_through(32*C + 7):
            if p <= 8*a:
                continue
            trial_p += 1
            power = p**a
            moment = sum((j+1)*p**j for j in range(a+1))
            gap = C*power - 8*moment
            assert gap > 0
            last_q = (3*C*power - 1) // (2*gap)
            for q in primes_through(last_q):
                if q == p or q <= 4*(a+1):
                    continue
                trial_q += 1
                top, bottom = C*power*q, moment*(2*q+1)
                div = gcd(top, bottom)
                b, c = bottom//div, top//div
                if 4*b < c < 5*b:
                    positive += 1
                for r, s in simple_pairs(b, c):
                    if not (q < r < s and p not in (r,s)):
                        continue
                    assert moment*(2*q+1)*(2*r+1)*(2*s+1) == C*power*q*r*s
                    # Even a composite candidate at this stage is reported.
                    hits += 1
                    if all(all(t % d for d in range(2, isqrt(t)+1)) for t in (r,s)):
                        print("prime completion", a, p, q, r, s)
                        prime_hits += 1
        yield a,trial_p,trial_q,positive,hits,prime_hits


if __name__ == "__main__":
    # Positive controls exercise each possible reduced denominator relation.
    for r, s in [(5,7), (7,13), (11,17), (7,19), (13,23)]:
        c, b = (2*r+1)*(2*s+1), r*s
        div = gcd(c,b)
        assert (r,s) in simple_pairs(b//div,c//div)
    print("a,prime_p,prime_pq,ratio_between_4_and_5,integer_completions,prime_completions")
    counts = list(cases())
    for row in counts:
        print(*row,sep=",")
    assert sum(row[-1] for row in counts) == 0
