"""Integer certificate for a counterexample to the A072633 rounding formula.

Run with Python 3. All enclosures use outward-rounded integers on a dyadic
grid. No floating-point arithmetic or computer algebra packages are required.
"""
N = int(
    "825938178725862470668731143853500055770827366427774395569242416121947420931438276432"
    "101429051717195553612323601798832846355583992322952343538822134069965039223614070919"
    "286865817634667434475142051826747655585028110155598130153493113423366879864589933523"
    "243147286414596703368678554144766303539160428257852463856280045877280683594018"
)
H = int(
    "238315382905732824756943412155054729570537689978422441384823237750366328830993618328"
    "821108375796700969709078659294570639312535094152867485080250315988292660731738784359"
    "096471947936116498878873318534887775697800474533440015020906028927664553859080067640"
    "8035615804839869621112379691761651672173609482508970267049685113823373707339171"
)
BITS = 3600
D = 1 << BITS
BITS_OF_N = bin(N)[3:]


def require(test, label):
    if not test:
        raise ArithmeticError(label)


def log_bound():
    """D times log(2) lies between the two returned integers."""
    terms = 1200
    lower = 0
    power = 3
    for j in range(terms):
        lower += (2 * D) // ((2 * j + 1) * power)
        power *= 9
    # Tail is less than (2 D / power) * (9/8), hence one grid unit.
    require(9 * D < 4 * power, "log-series remainder")
    return lower, lower + terms + 1


def power_bound(x, j, upper):
    """Integer enclosing D * ((x-j)/x)^N on the selected side."""
    extra = D - 1 if upper else 0
    base = (D * (x - j) + (x - 1 if upper else 0)) // x
    acc = base
    for bit in BITS_OF_N:
        acc = (acc * acc + extra) >> BITS
        if bit == '1':
            acc = (acc * base + extra) >> BITS
    return acc


def main():
    lo, hi = log_bound()
    rounded = (H - 1) // 2
    require(H == 2 * rounded + 1, "odd approximant")
    require((2 * rounded - 1) * hi < 2 * N * D < (2 * rounded + 1) * lo,
            "rounding N/log(2)")
    m = rounded + 1
    x = m + 1
    cutoff = 2400
    # Consecutive term ratios do not exceed ((x-1)/x)^N < 51/100.
    require(100 * power_bound(x, 1, True) < 51 * D, "tail ratio")
    upper = sum(power_bound(x, j, True) for j in range(1, cutoff + 1))
    # Sum of (51/100)^j for j>cutoff, times D, rounded up.
    tail_num = D * 51 ** (cutoff + 1)
    tail_den = 49 * 100 ** cutoff
    upper += (tail_num + tail_den - 1) // tail_den
    require(upper < D, "predicted m fails")
    lower = sum(power_bound(x+1, j, False) for j in range(1, 1251))
    require(lower > D, "next m works")
    print("Exponent digits:", len(str(N)))
    print("Predicted m:", m)
    print("Actual a(N):", m+1)
    print("10^665 times certified lower bound on the deficit at m:",
          (D - upper) * 10**665 // D)
    print("10^330 times certified lower bound on the excess at m+1:",
          (lower - D) * 10**330 // D)


if __name__ == "__main__":
    main()
