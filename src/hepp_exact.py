"""Exact comparison of Hepp bounds via residues modulo primes (Chinese remainder argument).

Let G have N edges and W = max omega(S). Put D = lcm(1..W). Each term of the ordering sum
prod_{k<N} 1/omega(S_k) times D^(N-1) is an integer in [1, D^(N-1)], and there are N! terms, so
X = D^(N-1) H(G) is an integer with 0 < X <= N! D^(N-1) =: B. For two graphs with the same N and W,
|X1 - X2| < B. If H1 = H2 modulo primes p_1..p_m (all > W) with p_1...p_m > B, then X1 = X2,
i.e. H1 = H2 exactly. A single prime with different residues proves H1 != H2."""
import math, os, subprocess
from concurrent.futures import ThreadPoolExecutor

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hepp_check")


def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):   # deterministic for n < 3.3e24
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_below(limit, count):
    out, n = [], limit - 1
    while len(out) < count:
        if is_prime(n):
            out.append(n)
        n -= 1
    return out


def ensure_built():
    """Compiles hepp_check.c next to this file if the binary is missing or older than the source."""
    if not os.path.exists(BIN) or os.path.getmtime(BIN) < os.path.getmtime(BIN + ".c"):
        subprocess.run([os.environ.get("CC", "cc"), "-O3", "-o", BIN, BIN + ".c"], check=True)


def graph_input(n, edges):
    return f"{n} {len(edges)}\n" + "".join(f"{a} {b}\n" for a, b in edges)


def run(n, edges, args):
    ensure_built()
    r = subprocess.run([BIN] + [str(a) for a in args], input=graph_input(n, edges),
                       capture_output=True, text=True)
    if r.returncode:
        raise RuntimeError(f"hepp_check failed ({r.returncode}): {r.stderr.strip()}")
    lines = r.stdout.split("\n")
    W = int(lines[0].split()[1])
    res = {}
    for line in lines[1:]:
        t = line.split()
        if t and t[0] == "mod":
            res[int(t[1])] = int(t[2])
        elif t and t[0] == "float":
            res["float"] = t[1]
    return W, res


def residues(n, edges, primes, jobs):
    """H(G) mod each prime, primes split over `jobs` parallel processes."""
    chunks = [primes[i::jobs] for i in range(jobs) if primes[i::jobs]]
    with ThreadPoolExecutor(len(chunks)) as ex:
        outs = list(ex.map(lambda c: run(n, edges, c), chunks))
    Ws = {W for W, _ in outs}
    assert len(Ws) == 1
    res = {}
    for _, r in outs:
        res.update(r)
    return Ws.pop(), [res[p] for p in primes]


def bound_bits(N, W):
    D = math.lcm(*range(1, W + 1))
    return (math.factorial(N) * D ** (N - 1)).bit_length()
