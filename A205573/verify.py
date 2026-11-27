"""Compare walks on the folded integer line, bounded matrices, and row series."""
from math import comb


def plain_path(n):
    return [(-1)**(j//2) * comb(n-j//2, j//2) if j%2 == 0 else 0
            for j in range(n+1)]


def exact_heights(j):
    hist = [0] * (j//2+1)
    for word in range(1 << j):
        z = high = 0
        for i in range(j):
            z += 1 if word & (1 << i) else -1
            high = max(high, z if z >= 0 else -z-1)
        if z in (0, -1):
            hist[high] += 1
    return hist


if __name__ == "__main__":
    histograms = [exact_heights(j) for j in range(15)]
    for n in range(13):
        p = plain_path(n)
        den = plain_path(n+1)
        for j, a in enumerate(p, 1):
            den[j] -= a
        v = [1] + [0] * n
        vals = []
        for j in range(45):
            vals.append(v[0])
            v = [v[0] + (v[1] if n else 0)] + [
                v[i-1] + (v[i+1] if i < n else 0) for i in range(1, n+1)]
            central = comb(j, j//2)
            if j <= 2*n+1:
                assert vals[j] == central
            elif j == 2*n+2:
                assert vals[j] == central - 1
            else:
                assert vals[j] < central
            if j < len(histograms):
                assert vals[j] == sum(histograms[j][:n+1])
            assert sum(den[h]*vals[j-h] for h in range(min(j+1, len(den)))) == (
                p[j] if j < len(p) else 0)
    print("13 matrix sizes, 45 powers, and every folded walk through length 14 checked.")
