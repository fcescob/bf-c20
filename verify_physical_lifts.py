#!/usr/bin/env python3
"""Remote consistency test of the mathematical lifting proof, not its proof.

Use arbitrary even gap inflation and unrelated orders of outside vertices.
Directly validate every edge of six perfect matchings in the resulting graph.
"""
from itertools import combinations
from pathlib import Path
import json
import random
from verify_local_construction import (connected_dominoes, even_complement,
                                       four_partition, odd_vectors)

rng = random.Random(20260904)


def inflate(order, flags, outside):
    gaps = list(flags)
    for _ in range((len(outside) - sum(gaps)) // 2):
        gaps[rng.randrange(len(gaps))] += 2
    spare = list(outside)
    rng.shuffle(spare)
    out, p = [], 0
    for i, v in enumerate(order):
        out.append(v)
        if i % 2:
            out.extend(spare[p:p + gaps[i // 2]])
            p += gaps[i // 2]
    assert p == len(spare)
    return out


def graph(c, d):
    m = len(c)
    edges = []
    for side, order in enumerate((c, d)):
        edges.extend((side*m + order[i], side*m + order[(i+1) % m]) for i in range(m))
    edges.extend((v, m+v) for v in range(m))
    assert len(edges) == 3*m
    return edges


def matching_for_class(c, d, s):
    m = len(c)
    matching = {2*m + v for v in s}
    for side, order in enumerate((c, d)):
        start = next(i for i, v in enumerate(order) if v in s)
        p = 1
        while p < m:
            i = (start + p) % m
            if order[i] in s:
                p += 1
            else:
                assert order[(i+1) % m] not in s
                matching.add(side*m + i)
                p += 2
    return matching


def check_pm(matching, edges, m):
    degree = [0] * (2*m)
    for e in matching:
        for v in edges[e]:
            degree[v] += 1
    assert len(matching) == m and all(x == 1 for x in degree)


def check_lift(k, d, cf, df):
    p = max(sum(cf), sum(df)) + 2*rng.randrange(11)
    outside = list(range(k, k+p))
    cfull = inflate(tuple(range(k)), cf, outside)
    dfull = inflate(d, df, outside)
    m = k+p
    edges = graph(cfull, dfull)
    n = matching_for_class(cfull, dfull, set(outside))
    check_pm(n, edges, m)
    if even_complement(d, cf, df):
        adjacent = [[] for _ in range(2*m)]
        for e, (a, b) in enumerate(edges):
            if e not in n:
                adjacent[a].append((b, e))
                adjacent[b].append((a, e))
        assert all(len(row) == 2 for row in adjacent)
        parts = [set(), set()]
        seen = set()
        for start in range(2*m):
            if start in seen:
                continue
            v, prev, count = start, -1, 0
            while True:
                assert v not in seen
                seen.add(v)
                nxt, e = next((a, b) for a, b in adjacent[v] if b != prev)
                parts[count % 2].add(e)
                count += 1
                v, prev = nxt, e
                if v == start:
                    break
            assert count % 2 == 0
        cover = [n, n, parts[0], parts[0], parts[1], parts[1]]
        kind = 'even'
    else:
        part = four_partition(d, cf, df)
        assert part is not None
        classes = [set(outside)] + [{x for x in range(k) if (s >> x) & 1} for s in part]
        cover = [set(range(2*m, 3*m))] + [matching_for_class(cfull, dfull, s) for s in classes]
        assert cover[1] == n
        kind = 'partition'
    for matching in cover:
        check_pm(matching, edges, m)
    assert all(sum(e in matching for matching in cover) == 2 for e in range(3*m))
    return kind, m


counts, largest = {}, 0
for k in (4, 6, 8, 10):
    vectors = odd_vectors(k//2)
    counts[k] = {'even': 0, 'partition': 0}
    for _ in range(500):
        while True:
            d = list(range(k))
            rng.shuffle(d)
            if connected_dominoes(d):
                break
        kind, m = check_lift(k, tuple(d), rng.choice(vectors), rng.choice(vectors))
        counts[k][kind] += 1
        largest = max(largest, 2*m)
print(json.dumps({'physical_lifts': counts, 'maximum_vertices': largest}, indent=2))
print('ALL ASSERTIONS PASSED: 2000 physical graphs, six explicit perfect matchings each')
