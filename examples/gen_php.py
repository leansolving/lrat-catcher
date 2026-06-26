#!/usr/bin/env python3
"""DIMACS for PHP(p, h): p pigeons into h holes (UNSAT iff p > h).

Variables: x_{i,j} = pigeon i (1..p) in hole j (1..h), index (i-1)*h + j.
Clauses: each pigeon in some hole; no two pigeons share a hole.

Usage: gen_php.py p h > php.cnf
"""
import sys

if len(sys.argv) != 3:
    sys.exit(__doc__)
p, h = int(sys.argv[1]), int(sys.argv[2])
var = lambda i, j: (i - 1) * h + j
clauses = [[var(i, j) for j in range(1, h + 1)] for i in range(1, p + 1)]
for j in range(1, h + 1):
    for i1 in range(1, p + 1):
        for i2 in range(i1 + 1, p + 1):
            clauses.append([-var(i1, j), -var(i2, j)])
print(f"p cnf {p * h} {len(clauses)}")
for c in clauses:
    print(*c, 0)
