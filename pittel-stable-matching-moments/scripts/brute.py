"""Naive brute force over ALL profiles, literally following the Lean definitions
(StableMarriage.Unbalanced.IsBlockingPair / IsStable), used to cross-check moments.c.
Usage: python3 -I brute.py n m   -> prints n m E[S] E[S^2] as exact fractions."""
import sys
from fractions import Fraction
from itertools import permutations, product


def main():
    n, m = int(sys.argv[1]), int(sys.argv[2])
    # rank arrays: firmRank i j = rank of worker j for firm i (a permutation of Fin m)
    pm = list(permutations(range(m)))
    pn = list(permutations(range(n)))
    injs = list(permutations(range(m), n))
    tot = s1 = s2 = 0
    for F in product(pm, repeat=n):
        for W in product(pn, repeat=m):
            S = 0
            for mu in injs:
                stable = True
                for i in range(n):
                    for j in range(m):
                        if mu[i] != j and F[i][j] < F[i][mu[i]] and all(
                                W[j][i] < W[j][k] for k in range(n) if mu[k] == j):
                            stable = False
                            break
                    if not stable:
                        break
                S += stable
            tot += 1
            s1 += S
            s2 += S * S
    print(n, m, Fraction(s1, tot), Fraction(s2, tot))


main()
