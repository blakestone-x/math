"""Rebuild the finite certificates and cross-check all entries of both prefixes."""
import argparse
from bisect import bisect_left, bisect_right
from collections import defaultdict
from functools import lru_cache
import gzip
import hashlib
import math
from pathlib import Path
import re
import shutil
import tempfile
from urllib.request import urlopen

from gaps import CATALOGUE, LIMIT, PRIMES, prefix, read_catalogue, rough_part, smooth_numbers, value
from rotations import LARGEST_C, audit

ORIGIN = ("https://raw.githubusercontent.com/bmatschke/solving-classical-diophantine-equations/"
          "97034f286c52b8e64f82bf00816a561aa01e26cd/s-unit-equation/")
PRIMES_16 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
SOURCES = {
    "radical": ("solutions_uptoRadical_10000000.txt",
                "c28a87a2015c987d6665647117094cab4e9072a7d23301c5d89f892d3d2b2fb3"),
    "primes": ("solutions_" + "_".join(map(str, PRIMES_16)) + ".txt",
               "80f3cd4e2535285f9a5c5811d9646b60523f7caef6fb0506202af761a743da98"),
}
COUNTS = (1, 4, 17, 63, 190, 545, 1433, 3649, 8828, 20015, 44641, 95358, 199081,
          412791, 839638, 1663449)
MAXIMA = (2, 9, 128, 4375, 18225, 1771561, 27295744, 1375325568, 6313843404, 289478389760,
          162618817224501, 162618817224501, 7401121252140000, 31266763186590547,
          3178648864589290499, 7058844079092540383)
OEIS_PREFIX = {
    5: (81,162,243,324,405,486,250,648,729,810,75,972,256,500,1215,1296,125,1458,144,1620,
        750,150,2048,1944,2025,512,2187,1000,125,2430,256,2592,225,250,1250,2916,32805,288,
        768,3240,81,1500,243,300,3645,4096,128,3888,625),
    7: (4375,8750,13125,17500,21875,26250,30625,35000,39375,43750,3136,52500,1728,61250,65625,
        70000,5120,78750,6144,87500,91875,6272,2048,105000,109375,3456,118125,122500,2430,131250,
        4000,140000,9408,10240,153125,157500,32805,12288,5184,175000),
}
ROW = re.compile(rb"(\d+): (\d+) \+ (\d+) = (\d+) \([\d.]+\)\s*")


def sha256_file(path):
    with path.open("rb") as handle:
        digest = hashlib.sha256()
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def triples(path, source):
    assert sha256_file(path) == SOURCES[source][1], "upstream SHA-256 mismatch"
    with path.open("rb") as handle:
        for line in handle:
            if line.startswith(b"#") or not line.strip():
                continue
            match = ROW.fullmatch(line)
            if match is None:
                raise ValueError(f"invalid triple record: {line!r}")
            radical, a, b, c = map(int, match.groups())
            assert 0 < a <= b and a + b == c and math.gcd(a, b) == 1
            product = a * b * c
            assert product % radical == 0 and pow(radical, product.bit_length(), product) == 0
            yield radical, a, b, c


def independent_prefix(p, limit):
    """Enumerate endpoints directly, using only the published global height bound."""
    smooth = smooth_numbers(PRIMES[p], LARGEST_C * limit)
    answer = [0] * (limit + 1)
    for i, x in enumerate(smooth):
        for j in range(bisect_left(smooth, x - limit, 0, i), i):
            gap = x - smooth[j]
            answer[gap] = x  # x increases
        upper = bisect_right(smooth, limit - x, 0, i + 1)
        for j in range(upper):
            answer[x + smooth[j]] = x
    return answer


def canonical_rows(grouped):
    kept = []
    for r, candidates in sorted(grouped.items()):
        block = []
        for d, u in sorted(candidates.items()):
            if any(d % e == 0 and u * e <= v * d for e, v in block):
                continue
            block.append((d, u))
        kept.extend((r, d, u) for d, u in block)
    return kept


def rebuild(path):
    prime_sets = {p: math.prod(primes) for p, primes in PRIMES.items()}
    grouped = {p: defaultdict(dict) for p in PRIMES}
    primitive = {p: set() for p in PRIMES}
    lean_tables = {
        "Families.lean": {"rowsFive":30, "rowsSeven":210, "rowsFiveWithEleven":330,
                          "rowsSevenWithEleven":2310},
        "Milestones.lean": {"rfive31":930, "rseven31":6510, "rfive281":8430, "rseven1849":9030,
                            "rfive583":17490, "rseven3737":784770},
    }
    small_tables = {product: [] for group in lean_tables.values() for product in group.values()}
    squarefree = bytearray([1]) * (LIMIT + 1)
    for i in range(2, math.isqrt(LIMIT) + 1):
        step = i*i
        squarefree[step::step] = bytes(LIMIT // step)
    height = count = 0
    for radical, a, b, c in triples(path, "radical"):
        count += 1
        height = max(height, c)
        assert radical <= LIMIT and squarefree[radical]
        for product, pairs in small_tables.items():
            if product % radical == 0:
                pairs.append((a, b))
        for p, primes in PRIMES.items():
            if math.lcm(radical, prime_sets[p]) > LIMIT:
                continue
            for d, u, v in ((a,c,b), (b,c,a), (c,b,a)):
                if rough_part(u, primes) != 1 or rough_part(v, primes) != 1:
                    continue
                r = rough_part(d, primes)
                ds = grouped[p][r]
                ds[d] = max(ds.get(d, 0), u)
                primitive[p].add((d, u))
    assert count == 432408 and height == LARGEST_C
    print(f"radical table: {count} rows, largest c = {height}")
    for filename, expected in lean_tables.items():
        lean = Path(__file__).with_name(filename).read_text()
        for name, product in expected.items():
            body = lean.split("def " + name + " :", 1)[1].split(":=", 1)[1].split("]", 1)[0]
            stored = [tuple(map(int, t)) for t in re.findall(r"\((\d+), (\d+)\)", body)]
            assert sorted(stored) == sorted(small_tables[product])
    print("all ten Lean triple lists match their complete upstream prime supports")
    lines = ["bound\trough\tgap\tendpoint\n"]
    for p in PRIMES:
        kept = canonical_rows(grouped[p])
        assert (len(primitive[p]), len(kept)) == {5:(6113,5123), 7:(20429,9813)}[p]
        print(f"{p}-smooth: {len(primitive[p])} primitive orientations, {len(kept)} retained maxima")
        multiplicities = defaultdict(int)
        for d, u in primitive[p]:
            multiplicities[rough_part(d, PRIMES[p])] += 1
        ambiguous = sum(m >= 2 for m in multiplicities.values())
        least = math.lcm(*(d for d, u in primitive[p] if rough_part(d, PRIMES[p]) == 1))
        assert (ambiguous, multiplicities[1], least) == {
            5:(466,50,1296000), 7:(3992,188,3360631680000)}[p]
        print(f"{ambiguous} certified rough parts admit multiple representations; "
              f"on smooth gaps the maximum multiplicity is {multiplicities[1]}, first at {least}")
        lines += [f"{p}\t{r}\t{d}\t{u}\n" for r,d,u in kept]
    return "".join(lines).encode("ascii")


def prime_maxima(path):
    product = math.prod(PRIMES_16)
    counts = [0] * len(PRIMES_16)
    best = [(0,0,0)] * len(PRIMES_16)

    @lru_cache(maxsize=None)
    def last_prime(radical):
        assert product % radical == 0
        return next(i for i in reversed(range(len(PRIMES_16))) if radical % PRIMES_16[i] == 0)

    for radical, a, b, c in triples(path, "primes"):
        i = last_prime(radical)
        counts[i] += 1
        best[i] = max(best[i], (c,a,b))
    for i in range(len(best)):
        c, a, b = max(best[:i+1])
        assert sum(counts[:i+1]) == COUNTS[i] and c == MAXIMA[i]
        if i >= 10:
            print(f"A376925({i+1}) = {a} + {b} = {c}")


def check_release():
    table = read_catalogue()
    for p in PRIMES:
        bound = LIMIT // math.prod(PRIMES[p])
        result = prefix(table, p, bound)
        assert result == independent_prefix(p, bound)
        known = OEIS_PREFIX[p]
        assert tuple(result[1:len(known)+1]) == known
        missing = result.index(0, 1)
        shortfall = next(n for n in range(1,bound+1) if 0 < result[n] < n)
        count = sum(bool(x) for x in result)
        assert (shortfall, result[shortfall], missing, count) == {
            5:(281,256,583,73096), 7:(1849,1800,3737,42257)}[p]
        for n in range(1, bound + 1):
            assert value(table, p, n) == result[n]
        for h in (1, 2**120*3**14, 5**250):
            assert value(table,p,h) == {5:81, 7:4375}[p]*h
            assert value(table,p,h*11**({5:4,7:5}[p]+80)) == 0
        assert value(table,p,11**{5:3,7:4}[p]) == {5:1250,7:18225}[p]
        digest = hashlib.sha256("".join(f"{n} {result[n]}\n" for n in range(1,bound+1)).encode()).hexdigest()
        print(f"{p}-smooth: all {bound} values agree, {count} nonzero, first shortfall "
              f"({shortfall}, {result[shortfall]}), first zero {missing}\nb-file SHA-256 {digest}")
    audit()


def main():
    if not __debug__:
        raise RuntimeError("this audit requires Python assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radical-file", type=Path)
    parser.add_argument("--primes-file", type=Path)
    parser.add_argument("--upstream", action="store_true", help="download missing input tables for this run")
    parser.add_argument("--rebuild-catalogue", action="store_true", help="write the derived compressed table")
    args = parser.parse_args()
    if args.rebuild_catalogue and not (args.radical_file or args.upstream):
        parser.error("rebuilding requires the radical table")
    with tempfile.TemporaryDirectory() as temp:
        for source, path in (("radical", args.radical_file), ("primes", args.primes_file)):
            if path is None and args.upstream:
                name = SOURCES[source][0]
                path = Path(temp, name)
                with urlopen(ORIGIN + name, timeout=180) as src, path.open("wb") as dst:
                    shutil.copyfileobj(src, dst)
            if path is None:
                continue
            if source == "radical":
                payload = rebuild(path)
                if args.rebuild_catalogue:
                    with CATALOGUE.open("wb") as file:
                        with gzip.GzipFile(filename="", mode="wb", fileobj=file, mtime=0) as archive:
                            archive.write(payload)
                assert gzip.decompress(CATALOGUE.read_bytes()) == payload
            else:
                prime_maxima(path)
        check_release()


if __name__ == "__main__":
    main()
