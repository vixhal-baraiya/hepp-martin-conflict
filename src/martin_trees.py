"""Martin invariant of a 4-regular graph by counting spanning-tree partitions.

Panzer-Yeats (arXiv:2304.05299, Theorem 1.3 / Corollary 5.18): for a 2k-regular graph G with at
least 3 vertices and any vertex v without self-loops, M(G) is the number of partitions of the edge
set of G - v into k spanning trees (unordered). For 4-regular G, k = 2.

This module counts those partitions by backtracking: every edge goes to tree A or tree B, both
stay forests, and the first edge goes to A (which makes the count unordered). With n vertices in
G - v and 2(n-1) edges, two forests of n-1 edges each are spanning trees. This shares no code
and no formula with the vertex recursion in martin_recursion.py."""
import sys


class UndoUF:
    def __init__(self, n):
        self.p = list(range(n)); self.sz = [1] * n; self.hist = []

    def find(self, x):
        while self.p[x] != x:
            x = self.p[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a == b:
            return False
        if self.sz[a] < self.sz[b]:
            a, b = b, a
        self.p[b] = a; self.sz[a] += self.sz[b]; self.hist.append(b)
        return True

    def undo(self):
        b = self.hist.pop(); a = self.p[b]; self.p[b] = b; self.sz[a] -= self.sz[b]


def bfs_edge_order(n, edges):
    """Order edges so that each one touches the part already seen (early cycle detection)."""
    adj = [[] for _ in range(n)]
    for i, (a, b) in enumerate(edges):
        adj[a].append(i); adj[b].append(i)
    seen_v, seen_e, order, queue = {0}, set(), [], [0]
    while queue:
        u = queue.pop(0)
        for i in adj[u]:
            if i not in seen_e:
                seen_e.add(i); order.append(edges[i])
                w = edges[i][0] + edges[i][1] - u
                if w not in seen_v:
                    seen_v.add(w); queue.append(w)
    assert len(order) == len(edges), "disconnected"
    return order


def two_tree_partitions(n, edges):
    if len(edges) != 2 * (n - 1):
        return 0
    E = bfs_edge_order(n, edges)
    A, B = UndoUF(n), UndoUF(n)
    cap = n - 1
    count = 0
    sys.setrecursionlimit(10000)

    def rec(i, na, nb):
        nonlocal count
        if i == len(E):
            count += 1
            return
        a, b = E[i]
        if na < cap and A.union(a, b):
            rec(i + 1, na + 1, nb); A.undo()
        if i > 0 and nb < cap and B.union(a, b):
            rec(i + 1, na, nb + 1); B.undo()
    rec(0, 0, 0)
    return count


def martin_by_trees(edges, v):
    """M(G) for a 4-regular graph G (edge list), deleting vertex v."""
    rest = sorted({x for e in edges for x in e} - {v})
    ix = {u: i for i, u in enumerate(rest)}
    return two_tree_partitions(len(rest), [(ix[a], ix[b]) for a, b in edges if v not in (a, b)])
