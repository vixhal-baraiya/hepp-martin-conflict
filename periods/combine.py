"""Combines the per-batch estimates of period.cpp logs: inverse-variance weighted mean, plain mean
with its empirical standard error, and chi^2 per degree of freedom of the batches."""
import math, re, sys


def combine(path):
    v = []
    for line in open(path):
        m = re.match(r"batch (\d+)\s+N=\S+\s+batch ([\d.]+) \+- ([\d.]+)", line)
        if m:
            v.append((float(m.group(2)), float(m.group(3))))
    w = [1 / s ** 2 for _, s in v]
    mu = sum(x * wi for (x, _), wi in zip(v, w)) / sum(w)
    se = 1 / math.sqrt(sum(w))
    xs = [x for x, _ in v]
    m = sum(xs) / len(xs)
    sd = math.sqrt(sum((x - m) ** 2 for x in xs) / (len(xs) - 1) / len(xs))
    chi2 = sum(((x - mu) / s) ** 2 for x, s in v) / (len(v) - 1)
    return len(v), mu, se, m, sd, chi2


if __name__ == "__main__":
    for p in sys.argv[1:]:
        n, mu, se, m, sd, chi2 = combine(p)
        print(f"{p}: {n} batches  weighted {mu:.3f} +- {se:.3f}   plain {m:.3f} +- {sd:.3f}   chi2/dof {chi2:.2f}")
