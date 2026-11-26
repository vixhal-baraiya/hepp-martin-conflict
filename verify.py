"""Verifies that three pairs of 13-loop phi^4 graphs have exactly equal Hepp bounds and exactly
different Martin sequences. Run from the repository root:  python3 verify.py [--jobs J]
Requires a C compiler (builds src/hepp_check) and Python 3.9+; no other dependencies."""
import argparse, math, os, sys, time
ROOT = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(ROOT, "src"))
from graphs import load_pairs, parse, decomplete, vertices, check_completed_primitive
from hepp_exact import primes_below, residues, run, bound_bits
from martin_trees import martin_by_trees
from martin_recursion import martin_r

ap = argparse.ArgumentParser()
ap.add_argument("--jobs", type=int, default=max(1, min(8, (os.cpu_count() or 2) - 1)))
ap.add_argument("--primes", type=int, default=24, help="number of primes below 2^30")
args = ap.parse_args()

primes = primes_below(1 << 30, args.primes)
t0 = time.time()
ok_all = True


def say(*a):
    print(*a, flush=True)


for i, pair in enumerate(load_pairs(), 1):
    say(f"\n=== Pair {i} ===")
    info = []
    for g in pair:
        E = parse(g["graph"])
        say(f"{g['nickel']}\n  structure: {check_completed_primitive(E)}")
        n, D = decomplete(E, 0)
        _, fl0 = run(n, D, ["float"])
        _, fl1 = run(*decomplete(E, max(vertices(E))), ["float"])
        W, res = residues(n, D, primes, args.jobs)
        m_trees = {martin_by_trees(E, v) for v in vertices(E)}
        assert len(m_trees) == 1, f"tree count depends on the vertex: {m_trees}"
        m1_trees = m_trees.pop()
        m1, m2 = martin_r(E, 1), martin_r(E, 2)
        assert m1 == m1_trees, f"Martin: recursion {m1} != spanning-tree count {m1_trees}"
        say(f"  Hepp bound (float, decompleted at vertex 0 / at vertex {max(vertices(E))}): {fl0['float']} / {fl1['float']}"
            f"   dataset: {g['data_hepp']}")
        say(f"  M(G)     = {m1}   (spanning-tree partitions at all {len(vertices(E))} vertices = vertex recursion;"
            f" dataset ln M1 {g['data_lnM1']}, ours {math.log(m1):.10f})")
        say(f"  M(G^[2]) = {m2}   (vertex recursion; dataset ln M2 {g['data_lnM2']}, ours {math.log(m2):.10f})")
        info.append(dict(N=len(D), W=W, res=res, m1=m1, m2=m2))
    a, b = info
    assert a["N"] == b["N"]
    W = max(a["W"], b["W"])
    need = bound_bits(a["N"], W)
    have = math.prod(primes).bit_length() - 1
    equal_mod = sum(x == y for x, y in zip(a["res"], b["res"]))
    hepp_equal = equal_mod == len(primes) and have >= need
    hepp_differ = equal_mod < len(primes)
    say(f"  Hepp residues agree modulo {equal_mod} of {len(primes)} primes below 2^30;"
        f" product of the primes >= 2^{have}, bound N! lcm(1..{W})^(N-1) < 2^{need}")
    say(f"  => Hepp bounds {'EXACTLY EQUAL' if hepp_equal else 'DIFFERENT' if hepp_differ else 'UNDECIDED (add primes)'}")
    first = 1 if a["m1"] != b["m1"] else 2 if a["m2"] != b["m2"] else None
    say(f"  => Martin sequences {'DIFFER at r = %d' % first if first else 'agree for r <= 2'}")
    ok_all &= hepp_equal and first is not None

say(f"\n{'VERIFIED' if ok_all else 'NOT VERIFIED'}: every pair has exactly equal Hepp bounds and different "
    f"Martin sequences ({time.time() - t0:.0f} s).")
say("By Panzer's Conjecture 1.2 (arXiv:1908.09820) each pair would have equal periods; by Panzer-Yeats "
    "Conjecture 1.10 (arXiv:2304.05299) each pair would have different periods. Both cannot hold.")
sys.exit(0 if ok_all else 1)
