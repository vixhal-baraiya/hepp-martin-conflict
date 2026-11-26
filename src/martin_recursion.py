"""Martin invariant by the vertex recursion (Panzer-Yeats, arXiv:2304.05299, Definition 1.1):
M(G) = 0 if G has a self-loop; M(G) = 1 if G has three vertices; otherwise
M(G) = sum over perfect matchings tau of the half-edges at a vertex v of M(G_tau), where G_tau
deletes v and joins its neighbours in pairs according to tau. Works for any 2k-regular multigraph,
so it also gives M(G^[r]), where every edge of G is replaced by r parallel edges."""
from collections import Counter


def _matchings(items):
    """Perfect matchings of a list of neighbour labels, grouped by the resulting multiset of pairs."""
    res = Counter()

    def rec(rest, acc):
        if not rest:
            res[tuple(sorted(acc))] += 1
            return
        a = rest[0]
        for i in range(1, len(rest)):
            rec(rest[1:i] + rest[i + 1:], acc + [tuple(sorted((a, rest[i])))])
    rec(list(items), [])
    return res


_cache = {}


def matchings(items):
    key = tuple(sorted(items))
    if key not in _cache:
        _cache[key] = _matchings(key)
    return _cache[key]


def elimination_order(edges):
    """Greedy min-degree order, which keeps the memo table small."""
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    rem, order = set(adj), []
    while len(rem) > 3:
        v = min(rem, key=lambda x: (len(adj[x] & rem), x))
        nb = adj[v] & rem
        for a in nb:
            adj[a] |= nb - {a}
        order.append(v); rem.remove(v)
    return order + sorted(rem)


def martin(edges, order):
    E = Counter(tuple(sorted(e)) for e in edges)
    if any(u == v for u, v in E):
        return 0
    memo = {}

    def M(state, remaining):
        if len(remaining) == 3:
            return 1
        if state in memo:
            return memo[state]
        v = remaining[0]
        half, base = [], {}
        for (a, b), m in state:
            if a == v:
                half += [b] * m
            elif b == v:
                half += [a] * m
            else:
                base[(a, b)] = m
        total = 0
        for pairs, cnt in matchings(half).items():
            if any(a == b for a, b in pairs):
                continue                      # G_tau has a self-loop, so M(G_tau) = 0
            nd = dict(base)
            for p in pairs:
                nd[p] = nd.get(p, 0) + 1
            total += cnt * M(frozenset(nd.items()), remaining[1:])
        memo[state] = total
        return total
    return M(frozenset(E.items()), tuple(order))


def martin_r(edges, r):
    """M(G^[r])."""
    return martin([e for e in edges for _ in range(r)], elimination_order(edges))
