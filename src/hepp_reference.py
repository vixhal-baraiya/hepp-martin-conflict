"""Hepp bound straight from its definition, for small graphs: the sum over all orderings of the
edges of prod_{k<N} 1/omega(first k edges), in exact rational arithmetic. Used only to test
hepp_check.c on small graphs, where N! orderings are affordable."""
from fractions import Fraction
from itertools import permutations


def rank(n, edges):
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    r = 0
    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb; r += 1
    return r


def omega(n, edges):
    return 2 * rank(n, edges) - len(edges)


def hepp_by_orderings(n, edges):
    N = len(edges); total = Fraction(0)
    for perm in permutations(range(N)):
        term = Fraction(1)
        for k in range(1, N):
            term /= omega(n, [edges[i] for i in perm[:k]])
        total += term
    return total


def hepp_by_subsets(n, edges):
    """Exact rational subset recursion f(S) = sum_{e in S} f(S-e)/omega(S) (bottom-up, the
    opposite direction to hepp_check.c), H = sum_e f(E-e)."""
    N = len(edges); full = (1 << N) - 1
    f = [Fraction(0)] * (1 << N); f[0] = Fraction(1)
    for S in range(1, full):
        sub = [edges[i] for i in range(N) if S >> i & 1]
        w = omega(n, sub)
        assert w > 0, "not primitive"
        f[S] = sum(f[S & ~(1 << i)] for i in range(N) if S >> i & 1) / w
    return sum(f[full & ~(1 << i)] for i in range(N))
