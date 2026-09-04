#!/usr/bin/env python3
"""Bounded exact test of a proposed local C(20) construction; run remotely.

Candidate: on a single alternating circuit with k<=10 spoke positions,
either its complementary 2-factor is even, or its positions partition
into four common-good odd sets. Either conclusion would construct BF.
Failure is only failure of this stronger local construction.
"""
from itertools import permutations, combinations
from pathlib import Path
import json
import random


def odd_vectors(n):
    return [tuple((w >> i) & 1 for i in range(n)) for w in range(1 << n)
            if bin(w).count('1') % 2]


def root_functions(k):
    p = list(range(k))
    def find(x):
        while p[x] != x:
            x = p[x]
        return x
    def join(x, y):
        p[find(x)] = find(y)
    return find, join


def connected_dominoes(d):
    k = len(d)
    find, join = root_functions(k)
    for i in range(0, k, 2):
        join(i, i+1)
        join(d[i], d[i+1])
    return len({find(x) for x in range(k)}) == 1


def even_complement(d, cflags, dflags):
    k = len(d)
    find, join = root_functions(k)
    edges = []
    for j in range(k//2):
        a, b = 2*j+1, (2*j+2) % k
        edges += [(a, b, cflags[j]), (d[a], d[b], dflags[j])]
        join(a, b)
        join(d[a], d[b])
    weights = {}
    for a, b, w in edges:
        r = find(a)
        weights[r] = weights.get(r, 0) ^ w
    return all(w == 0 for w in weights.values())


def parity_field(order, flags):
    pref = 0
    out = {}
    for i, x in enumerate(order):
        out[x] = pref
        pref ^= 1 if i % 2 == 0 else 1 ^ flags[i//2]
    assert pref == 1
    return out


def is_good(mask, order, field):
    bits = [field[x] for x in order if (mask >> x) & 1]
    return bool(bits) and bits[0] == bits[-1] and all(a != b for a, b in zip(bits, bits[1:]))


def four_partition(d, cf, df):
    k = len(d)
    if k == 4:
        return [1 << x for x in range(k)]
    c = tuple(range(k))
    cp, dp = parity_field(c, cf), parity_field(d, df)
    good = {s: [] for s in (3, 5, 7) if s <= k-3}
    for size in good:
        for comb in combinations(range(k), size):
            mask = sum(1 << x for x in comb)
            if is_good(mask, c, cp) and is_good(mask, d, dp):
                good[size].append(mask)
    full = (1 << k) - 1
    if good.get(k-3):
        a = good[k-3][0]
        return [a] + [1 << x for x in range(k) if not (a >> x) & 1]
    if k == 6:
        return None
    if k == 8:
        for a, b in combinations(good[3], 2):
            if not a & b:
                return [a, b] + [1 << x for x in range(k) if not ((a | b) >> x) & 1]
        return None
    assert k == 10
    for a in good[5]:
        for b in good[3]:
            if not a & b:
                return [a, b] + [1 << x for x in range(k) if not ((a | b) >> x) & 1]
    for a, b, e in combinations(good[3], 3):
        if not (a & b or a & e or b & e):
            return [a, b, e, full ^ (a | b | e)]
    return None


def independent_good(mask, order, flags):
    k = len(order)
    selected = [i for i, x in enumerate(order) if (mask >> x) & 1]
    if not selected:
        return False
    for t, i in enumerate(selected):
        j = selected[(t+1) % len(selected)]
        q, par = i, 0
        while True:
            par ^= 1 if q % 2 == 0 else 1 ^ flags[q//2]
            q = (q+1) % k
            if q == j:
                break
        if par != 1:
            return False
    return True


def independent_partition(d, cf, df):
    """Generic exact cover recursion, independent of the size-pattern shortcut."""
    k = len(d)
    masks = [s for s in range(1, 1 << k) if bin(s).count('1') % 2
             and independent_good(s, tuple(range(k)), cf)
             and independent_good(s, d, df)]
    def rec(rem, n):
        if n == 1:
            return [rem] if rem in masks else None
        least = rem & -rem
        for mask in masks:
            if mask & least and not mask & ~rem and bin(rem ^ mask).count('1') >= n-1:
                ans = rec(rem ^ mask, n-1)
                if ans is not None:
                    return [mask] + ans
        return None
    return rec((1 << k)-1, 4)


def main():
    rng = random.Random(20260904)
    counts, failure = {}, None
    for k in (6, 8, 10):
        vectors = odd_vectors(k//2)
        if k == 6:
            cases = ((d, cf, df) for tail in permutations(range(1, k))
                     if connected_dominoes(d := (0,) + tail)
                     for cf in vectors for df in vectors)
        else:
            def sampled():
                seen = set()
                while len(seen) < 2000:
                    tail = list(range(1, k))
                    rng.shuffle(tail)
                    d = (0,) + tuple(tail)
                    if connected_dominoes(d):
                        case = (d, rng.choice(vectors), rng.choice(vectors))
                        if case not in seen:
                            seen.add(case)
                            yield case
            cases = sampled()
        row = {'tested': 0, 'even': 0, 'partition': 0}
        for d, cf, df in cases:
            row['tested'] += 1
            if even_complement(d, cf, df):
                row['even'] += 1
                continue
            part = four_partition(d, cf, df)
            if part is not None:
                assert len(part) == 4
                assert sum(part) == (1 << k)-1
                assert all(independent_good(s, tuple(range(k)), cf)
                           and independent_good(s, d, df) for s in part)
                row['partition'] += 1
            else:
                assert independent_partition(d, cf, df) is None
                failure = {'k': k, 'D': d, 'C_flags': cf, 'D_flags': df}
                print('FAILED LOCAL CONSTRUCTION', failure, flush=True)
                break
        counts[k] = row
        print(k, row, flush=True)
        if failure:
            break
    Path('out').mkdir(exist_ok=True)
    Path('out/probe.json').write_text(json.dumps({'counts': counts, 'failure': failure}, indent=2) + '\n')
    print('ALL ASSERTIONS PASSED; a failure is not a BF counterexample', flush=True)


if __name__ == '__main__':
    main()
