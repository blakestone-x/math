"""Independent full-word graph for the four-pair bound, with both borrow phases."""
from functools import lru_cache

def check(pairs):
    modulus = 1 << pairs
    reverse = [int(f'{x:0{pairs}b}'[::-1], 2) for x in range(modulus)]
    graph = {}
    for low in range(modulus):
        for high in range(modulus):
            for inner in (0, 1):
                source = low, high, inner
                graph[source] = []
                for incoming in (0, 1):
                    lower = low - reverse[high] - incoming
                    if int(lower < 0) != inner:
                        continue
                    upper = high - reverse[low] - inner
                    target = lower % modulus, upper % modulus, 1 - inner
                    graph[source].append((target, incoming, int(upper < 0)))

    # All recurrent pairs of full-word states alternate with their complements.
    # Collapse the two endpoints of each such cycle; unrelated states stay separate.
    representative = {v: v for v in graph}
    marked = set()
    for v, edges in graph.items():
        for w, a, h in edges:
            if any(u == v for u, _, _ in graph[w]):
                assert a == h and w == (modulus-1-v[0], modulus-1-v[1], 1-v[2])
                representative[v] = representative[w] = min(v, w)
                marked.add(min(v, w))
    edges = {v: set() for v in representative.values()}
    for v, items in graph.items():
        for w, _, _ in items:
            if representative[v] != representative[w]:
                edges[representative[v]].add(representative[w])

    @lru_cache(None)
    def longest(v):
        return int(v in marked) + max((longest(w) for w in edges[v]), default=0)

    return len(marked), max(longest(v) for v in edges)

if __name__ == '__main__':
    for k, expected in enumerate([2, 4, 5, 5, 7, 9], 1):
        assert check(k) == (1 << k, expected)
        print(f'{k} pairs: {1 << k} recurrent components, at most {expected} on a path.')
