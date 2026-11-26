"""Graph input and structural checks for completed primitive phi^4 graphs."""
import json, os, re
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data", "graphs.json")


def parse(graph_string):
    """Edges of a graph written as G([{u,v},w],...) in Balduf's files (w is always 1 here)."""
    edges = []
    for u, v, w in re.findall(r"\[\{(\d+),(\d+)\},(\d+)\]", graph_string):
        edges += [(int(u), int(v))] * int(w)
    return edges


def load_pairs():
    return json.load(open(DATA))["pairs"]


def vertices(edges):
    return sorted({x for e in edges for x in e})


def decomplete(edges, v):
    """Delete vertex v; relabel the rest 0..n-1. Returns (n, edge list)."""
    rest = [u for u in vertices(edges) if u != v]
    ix = {u: i for i, u in enumerate(rest)}
    return len(rest), [(ix[a], ix[b]) for a, b in edges if v not in (a, b)]


def check_completed_primitive(edges):
    """Checks that G is a simple 4-regular graph whose only 4-edge cuts isolate a single vertex
    (equivalently: cyclically 6-edge-connected; equivalently: G minus any vertex is a primitive
    log-divergent phi^4 graph). Returns a short description; raises on failure."""
    vs = vertices(edges)
    n = len(vs)
    assert vs == list(range(n)), "vertices must be 0..n-1"
    assert all(a != b for a, b in edges), "self-loop"
    assert len(set(tuple(sorted(e)) for e in edges)) == len(edges), "multiple edge"
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    assert all(d == 4 for d in deg), "not 4-regular"
    smallest = None
    for mask in range(1, 1 << n):
        if not mask & 1:            # S contains vertex 0; complement covers the rest
            continue
        k = bin(mask).count("1")
        if k < 2 or k > n - 2:
            continue
        cut = sum(((mask >> a) ^ (mask >> b)) & 1 for a, b in edges)
        smallest = cut if smallest is None else min(smallest, cut)
        assert cut >= 6, f"nontrivial edge cut of size {cut}"
    return f"{n} vertices, {len(edges)} edges, 4-regular, simple, smallest nontrivial edge cut {smallest}"
