"""c2 invariant at a prime p from the Martin sequence (Panzer-Yeats, arXiv:2304.05299, Theorem 1.8):
for a 4-regular graph G with at least 6 vertices, every prime p and any vertex v,

    c2^(p)(G - v) = M(G^[p-1]) / (3p)  mod p,

where the quotient is a p-adic integer (3 is inverted modulo p when p != 3)."""
from fractions import Fraction


def c2_from_martin(m, p):
    q = Fraction(m, 3 * p)
    assert q.denominator % p != 0, "M(G^[p-1]) / (3p) is not p-integral"
    return q.numerator * pow(q.denominator, -1, p) % p
