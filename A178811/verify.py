"""Deterministic certificate of a powerful pair with identical prime signatures."""

from functools import cache
from math import isqrt, prod


SMALLER = 12060988175814077525103089858803400807061146388053160933788947402094570694643847
LEFT = {23: 3, 1361: 2, 39157289: 2, 13475265289: 2, 43842128059343041: 2}
RIGHT = {2: 3, 3: 2, 13: 2, 509: 2, 61853469184829429986091801293807909: 2}

# Aaron Meyerowitz posted X and Y in his 2010 MathOverflow answer.
MEYEROWITZ_X = 1280501243627863240958544690009528057630666112209166210134539296491713575228511562822601
MEYEROWITZ_Y = 195559058652792360721040748497175750756141280467009959592151199119238991562483618043657
X_FACTORS = (953, 3571, 12511, 18803, 26041, 50298511, 45065539,
             1471929336078698099, 18409151278361767128991817965934729)
Y_FACTORS = (41, 97, 137, 6359, 14281, 772207, 748273,
             1843316936777394280035161, 3710739893777571587812098928531145777)

# Each entry supplies a witness and the complete prime factorization of p - 1.
# The remaining primes are small enough to check by trial division.
CERTIFICATES = {
    13475265289: (7, {2: 3, 3: 1, 17: 1, 33027611: 1}),
    43842128059343041: (19, {2: 6, 3: 1, 5: 1, 7: 1, 17: 1, 599: 1, 640688029: 1}),
    640688029: (2, {2: 2, 3: 1, 1361: 1, 39229: 1}),
    61853469184829429986091801293807909: (
        2, {2: 2, 3: 1, 33181: 1, 130844895031: 1, 1187234650202556569: 1}
    ),
    130844895031: (7, {2: 1, 3: 2, 5: 1, 1453832167: 1}),
    1453832167: (5, {2: 1, 3: 1, 242305361: 1}),
    242305361: (6, {2: 4, 5: 1, 11: 1, 251: 1, 1097: 1}),
    1187234650202556569: (3, {2: 3, 1151: 1, 19051: 1, 6767892871: 1}),
    6767892871: (3, {2: 1, 3: 1, 5: 1, 79: 1, 797: 1, 3583: 1}),
    1471929336078698099: (6, {2: 1, 7: 1, 17: 1, 109: 1, 53087: 1, 1068797237: 1}),
    1068797237: (2, {2: 2, 13: 2, 1581061: 1}),
    18409151278361767128991817965934729: (
        6, {2: 3, 7: 1, 13: 1, 17: 1, 67: 1, 269: 1, 655483069: 1, 12392879: 1, 10159976311: 1}
    ),
    655483069: (6, {2: 2, 3: 2, 127: 1, 307: 1, 467: 1}),
    10159976311: (3, {2: 1, 3: 1, 5: 1, 11: 1, 4073: 1, 7559: 1}),
    1843316936777394280035161: (3, {2: 3, 5: 1, 53: 1, 2919667: 1, 297804208877729: 1}),
    297804208877729: (13, {2: 5, 7: 2, 189926153621: 1}),
    189926153621: (3, {2: 2, 5: 1, 7: 1, 1356615383: 1}),
    1356615383: (5, {2: 1, 11353: 1, 59747: 1}),
    3710739893777571587812098928531145777: (
        3, {2: 4, 29: 1, 6619: 1, 8536459: 1, 1092758047: 1, 129523442780057: 1}
    ),
    1092758047: (3, {2: 1, 3: 1, 6949: 1, 26209: 1}),
    129523442780057: (3, {2: 3, 13: 2, 181211: 1, 528673: 1}),
}


def multiply(factors):
    return prod(prime**exponent for prime, exponent in factors.items())


def require(condition, message):
    if not condition:
        raise ValueError(message)


@cache
def prove_prime(p):
    if p < 100_000_000:
        require(p >= 2 and all(p % d for d in range(2, isqrt(p) + 1)),
                f"Failed trial division at {p}")
        return
    g, factors = CERTIFICATES[p]
    require(multiply(factors) == p - 1, f"Incomplete factorization of {p} - 1")
    for q in factors:
        prove_prime(q)
        require(pow(g, (p - 1) // q, p) != 1, f"Order witness failed at {p}, {q}")
    require(pow(g, p - 1, p) == 1, f"Fermat congruence failed at {p}")


def count_signatures_at_most(limit):
    # A least representative uses consecutive primes with decreasing or equal
    # exponents. Branch recursively over all such products at most the limit.
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]
    require(prod(primes) > limit, "Prime list too short")

    def count(value, index, exponent_bound):
        total = 1
        for exponent in range(1, exponent_bound + 1):
            value *= primes[index]
            if value > limit:
                break
            total += count(value, index + 1, exponent)
        return total

    return count(1, 0, limit.bit_length())


def verify():
    for prime in LEFT.keys() | RIGHT.keys():
        prove_prime(prime)
    require(multiply(LEFT) == SMALLER, "Left factorization mismatch")
    require(multiply(RIGHT) == SMALLER + 1, "Right factorization mismatch")
    require(sorted(LEFT.values()) == sorted(RIGHT.values()) == [2, 2, 2, 2, 3],
            "Prime signatures differ")

    # The real part of (24335 + 3588 sqrt(46))^17 is 2*SMALLER + 1.
    real, radical = 1, 0
    for _ in range(17):
        real, radical = (24335*real + 46*3588*radical, 3588*real + 24335*radical)
    require(real**2 - 46*radical**2 == 1 and real == 2*SMALLER + 1,
            "Pell construction mismatch")

    least = 2**3 * (3*5*7*11)**2
    require(least == 10_672_200 and count_signatures_at_most(least) == 499,
            "Least representative or its index differs")
    prove_prime(least + 1)
    print("Certified the 80-digit counterexample at index 499.")

    for factors, value, cube_prime in ((X_FACTORS, MEYEROWITZ_X, 2),
                                       (Y_FACTORS, MEYEROWITZ_Y, 7)):
        require(len(set(factors)) == len(factors) == 9 and cube_prime not in factors,
                "Expected nine distinct primes, each different from the cubed prime")
        require(prod(factors) == value, "2010 factorization mismatch")
        for p in factors:
            prove_prime(p)
    require(8*MEYEROWITZ_X**2 - 343*MEYEROWITZ_Y**2 == 1, "2010 pair is not consecutive")
    print("Certified the 176-digit example of Meyerowitz (2010).")


if __name__ == "__main__":
    verify()
