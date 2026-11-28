"""Construct the acyclic matching from the spanning-tree coloring proof."""
import sys


def read_graph6(line):
    data = line.strip()
    n = ord(data[0]) - 63
    assert 1 <= n < 63
    graph = [set() for _ in range(n)]
    bit = 0
    for j in range(1, n):
        for i in range(j):
            if (ord(data[1 + bit//6]) - 63) & (32 >> (bit % 6)):
                graph[i].add(j)
                graph[j].add(i)
            bit += 1
    return graph


def construct_matching(graph):
    n = len(graph)
    assert max(map(len, graph)) <= 3
    order = [0]
    parent = {0: None}
    children = [[] for _ in graph]
    for v in order:
        for w in sorted(graph[v]):
            if w not in parent:
                order.append(w)
                parent[w] = v
                children[v].append(w)
    assert len(order) == n
    tree_degree = [len(ch) + (parent[v] is not None) for v, ch in enumerate(children)]
    chords = [(v,w) for v in order for w in sorted(graph[v])
              if v < w and parent[v] != w and parent[w] != v]
    partner = {}
    for v,w in chords:
        if tree_degree[v] == tree_degree[w] == 2:
            assert v not in partner and w not in partner
            partner[v] = w
            partner[w] = v

    missing = {}
    incoming = {}
    matchings = [set() for _ in range(3)]
    for v in order:
        available = {0,1,2} - {incoming.get(v)}
        if parent[v] is not None and tree_degree[v] == 2:
            # There are two legal missing colors; at most one is forbidden.
            miss = min(available - {missing.get(partner.get(v))})
            missing[v] = miss
            colors = [min(available - {miss})]
        else:
            colors = sorted(available)[:len(children[v])]
            if tree_degree[v] == 2:
                missing[v] = min(available - set(colors))
        for w,color in zip(children[v], colors):
            incoming[w] = color
            matchings[color].add((v,w))
    for v,w in chords:
        conflict = 0
        for matching in matchings:
            touching_v = next((edge for edge in matching if v in edge), None)
            if touching_v and any(w in edge for edge in matching):
                matching.remove(touching_v)
                conflict += 1
        assert conflict <= 1
    assert sum(map(len,matchings)) >= n-1-len(chords)
    answer = max(matchings, key=len)
    selected = {v for edge in answer for v in edge}
    assert len(selected) == 2*len(answer)
    assert all(not (v in selected and w in selected) for v,w in chords)
    return answer


if __name__ == '__main__':
    count = 0
    for line in sys.stdin:
        construct_matching(read_graph6(line))
        count += 1
    print(f'Spanning-tree construction verified on {count} connected subcubic graphs.')
