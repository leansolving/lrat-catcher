#!/usr/bin/env python3
"""Emit iCNF static-split cubes: all 2^k sign patterns on variables 1..k.

Usage: gen_static_cubes.py k > cubes.icnf
"""
import itertools
import sys

if len(sys.argv) != 2:
    sys.exit(__doc__)
k = int(sys.argv[1])
for signs in itertools.product((1, -1), repeat=k):
    print("a", *(v * s for v, s in zip(range(1, k + 1), signs)), 0)
