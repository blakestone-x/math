"""Direct polynomial multiplication of the two proposed products."""
def left_series(limit, shift):
    out = [0] * (limit + 1)
    for n in range(1, limit + 1):
        degree = limit - n
        poly = [1] + [0] * degree
        for k in range(2 * n - shift, degree + 1):
            for j in range(degree, k - 1, -1):
                poly[j] -= poly[j-k]
        for j, val in enumerate(poly):
            out[j+n] += val
    return out


def right_series(limit, linear):
    out = [0] * (limit + 1)
    for m in range(-limit, limit + 1):
        exponent = 4 * m * m + linear * m + 1
        if exponent <= limit:
            out[exponent] += 1
    return out


if __name__ == "__main__":
    for shift, linear in ((0, 3), (1, 1)):
        assert left_series(200, shift) == right_series(200, linear)
    print("Both identities agree coefficient by coefficient through q^200.")
