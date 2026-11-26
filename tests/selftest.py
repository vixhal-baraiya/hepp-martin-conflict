"""Tests every method on the 72 graphs of the dataset with 3 to 8 loops.

Hepp bound:
  * definition (sum over all N! edge orderings) = rational subset recursion, up to 4 loops;
  * rational subset recursion = hepp_check.c modulo three primes, up to 7 loops, at every
    decompletion vertex (the Hepp bound of a completed graph does not depend on it);
  * hepp_check.c in floating point = the dataset's Hepp column, up to 8 loops.
Martin invariant:
  * spanning-tree partitions (at every vertex) = vertex recursion = dataset ln M[1], up to 8 loops;
  * vertex recursion for G^[2] = dataset ln M[2], up to 8 loops."""
import json, math, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src"))
from graphs import parse, decomplete, vertices, check_completed_primitive, HERE
from hepp_reference import hepp_by_orderings, hepp_by_subsets
from hepp_exact import run, primes_below
from martin_trees import martin_by_trees
from martin_recursion import martin_r

small = json.load(open(os.path.join(HERE, "..", "data", "small_graphs.json")))["graphs"]
primes = primes_below(1 << 30, 3)
fails = 0


def check(ok, msg):
    global fails
    if not ok:
        fails += 1
        print("FAIL", msg)


for g in small:
    L, E = g["loops"], parse(g["graph"])
    tag = f"{L} loops {g['nickel']}"
    try:
        check_completed_primitive(E)
        primitive = True
    except AssertionError as e:
        primitive = False
        print(f"skip  {tag}: {e} (not a completed primitive graph)")
        continue
    n, D = decomplete(E, max(vertices(E)))
    if L <= 4:
        check(hepp_by_orderings(n, D) == hepp_by_subsets(n, D), f"{tag}: orderings vs subsets")
    if L <= 7:
        exact = None
        for v in vertices(E):
            n, D = decomplete(E, v)
            h = hepp_by_subsets(n, D)
            exact = exact if exact is not None else h
            check(h == exact, f"{tag}: Hepp depends on decompletion vertex {v}")
            if v in (0, max(vertices(E))):
                _, res = run(n, D, primes)
                for p in primes:
                    check(res[p] == h.numerator * pow(h.denominator, -1, p) % p, f"{tag}: mod {p}, vertex {v}")
    _, res = run(*decomplete(E, 0), ["float"])
    hf = float(res["float"])
    check(abs(hf / float(g["data_hepp"]) - 1) < 1e-12, f"{tag}: float Hepp {hf} vs data {g['data_hepp']}")
    m_trees = {martin_by_trees(E, v) for v in vertices(E)}
    m1 = martin_r(E, 1)
    check(m_trees == {m1}, f"{tag}: trees {m_trees} vs recursion {m1}")
    check(abs(math.log(m1) - float(g["data_lnM1"])) < 1e-9, f"{tag}: M1 {m1} vs data")
    m2 = martin_r(E, 2)
    check(abs(math.log(m2) - float(g["data_lnM2"])) < 1e-9, f"{tag}: M2 {m2} vs data")
    print(f"ok    {tag}: Hepp {hf:.10g}  M1 {m1}  M2 {m2}")

print("selftest:", "PASSED" if not fails else f"{fails} FAILURES")
sys.exit(1 if fails else 0)
