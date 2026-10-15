#!/usr/bin/env python3
"""Independent finite rational Schur tests for outward b=4 and full-neighbor b=5 stars.

Python numbers here are ONLY a diagnostic outside mathematical Lean sources.
"""
from fractions import Fraction

def invert(a):
    n = len(a)
    q = [[Fraction(a[i][j]) for j in range(n)] +
         [Fraction(i == j) for j in range(n)] for i in range(n)]
    for k in range(n):
        pivot = next(i for i in range(k, n) if q[i][k] != 0)
        q[k], q[pivot] = q[pivot], q[k]
        d = q[k][k]
        q[k] = [x / d for x in q[k]]
        for i in range(n):
            if i != k:
                c = q[i][k]
                q[i] = [q[i][j] - c * q[k][j] for j in range(2 * n)]
    return [row[n:] for row in q]

def mm(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Fraction(0))
             for j in range(len(b[0]))] for i in range(len(a))]

def star(m):
    n = m + 1
    L = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i in range(m):
        L[i][i] = 1
        L[i][m] = L[m][i] = -1
    L[m][m] = m
    return L

def reduce(L, B):
    n = len(L)
    I = [j for j in range(n) if j not in B]
    d = [[L[i][j] for j in B] for i in B]
    if I:
        x = mm([[L[i][j] for j in I] for i in B],
               invert([[L[i][j] for j in I] for i in I]))
        x = mm(x, [[L[i][j] for j in B] for i in I])
        d = [[d[i][j] - x[i][j] for j in range(len(B))]
             for i in range(len(B))]
    z = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for i, u in enumerate(B):
        for j, v in enumerate(B):
            z[u][v] = d[i][j]
    return tuple(tuple(row) for row in z)

def main():
    L = star(4)
    groups = {}
    for mask in range(1, 1 << 5):
        B = tuple(i for i in range(5) if mask & (1 << i))
        groups.setdefault(reduce(L, B), []).append(B)
    assert sum(map(len, groups.values())) == 31
    assert len(groups) == 27
    zero = tuple(tuple(Fraction(0) for _ in range(5)) for _ in range(5))
    assert set(groups[zero]) == {(i,) for i in range(5)}
    assert all(len(v) == 1 for k, v in groups.items() if k != zero)

    # Resistance polarization: root-to-child=1; distinct-child=2
    G = [[(Fraction(1) + Fraction(1) - (Fraction(0) if i == j else Fraction(2)))/2
          for j in range(4)] for i in range(4)]
    assert G == [[Fraction(i == j) for j in range(4)] for i in range(4)]

    # Full degree-five interior-node elimination; 5 neighbors, 1/5 effective conductance.
    F = reduce(star(5), tuple(range(5)))
    assert all(F[i][j] == (-Fraction(1, 5) if i != j else Fraction(4, 5))
               for i in range(5) for j in range(5))
    print("PASS: 31 boundaries, 27 responses, 5 singleton-zero collapse")
    print("PASS: G_res=I_4, full-degree-five K5 coefficient=1/5")
    print("These are finite diagnostics, not Lean theorem verification.")

if __name__ == "__main__":
    main()
