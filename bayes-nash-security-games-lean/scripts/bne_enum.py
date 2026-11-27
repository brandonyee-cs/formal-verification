#!/usr/bin/env python3
"""Exact (Fraction) support enumeration of Bayes-Nash equilibria for small Bayesian simple
security games, in the marginal-coverage model of the formal-conjectures statement
Arxiv.2610.08796.exists_isPolyTime_bayesNash.  Every candidate is re-checked by an
independent implementation of GameInput.IsBayesNash (check_bne below).

Usage: python3 -I scripts/bne_enum.py [seed] [num_games] [payoff_bound]
(payoff_bound 5 = degenerate small-integer games incl. zero priors; e.g. 1000 = generic games)
"""
import sys, itertools, random
from fractions import Fraction as F

def check_bne(r, dpay, types, cov, rows):
    """Literal transcription of GameInput.IsBayesNash (for a valid game)."""
    n, k = len(dpay), len(types)
    if len(cov) != n or len(rows) != k: return False
    if sum(cov) != r: return False
    if any(not (0 <= c <= 1) for c in cov): return False
    for row in rows:
        if len(row) != n or sum(row) != 1 or any(a < 0 for a in row): return False
    for (p, ap), row in zip(types, rows):
        U = [(1 - cov[t]) * ap[t][0] + cov[t] * ap[t][1] for t in range(n)]
        for t in range(n):
            if row[t] > 0 and any(U[s] > U[t] for s in range(n)): return False
    gain = [sum(p * row[t] for (p, _), row in zip(types, rows)) * (dpay[t][1] - dpay[t][0])
            for t in range(n)]
    for t in range(n):
        for s in range(n):
            if cov[t] > 0 and cov[s] < 1 and gain[s] > gain[t]: return False
    return True

def solve_linear(A, b):
    """Exact Gaussian elimination; returns one solution (free vars = 0) or None."""
    m, nv = len(A), (len(A[0]) if A else 0)
    M = [row[:] + [bb] for row, bb in zip(A, b)]
    piv, ri = [], 0
    for ci in range(nv):
        p = next((i for i in range(ri, m) if M[i][ci] != 0), None)
        if p is None: continue
        M[ri], M[p] = M[p], M[ri]
        pv = M[ri][ci]; M[ri] = [x / pv for x in M[ri]]
        for i in range(m):
            if i != ri and M[i][ci] != 0:
                f = M[i][ci]; M[i] = [x - f * y for x, y in zip(M[i], M[ri])]
        piv.append(ci); ri += 1
        if ri == m: break
    for i in range(ri, m):
        if M[i][nv] != 0: return None
    x = [F(0)] * nv
    for i, ci in enumerate(piv): x[ci] = M[i][nv]
    return x

def equilibria(r, dpay, types):
    n, k = len(dpay), len(types)
    subsets = [s for L in range(1, n + 1) for s in itertools.combinations(range(n), L)]
    found = []
    for status in itertools.product((0, 1, 2), repeat=n):  # 0: c=0, 1: interior, 2: c=1
        if sum(1 for s in status if s == 2) > r: continue
        interior = [t for t in range(n) if status[t] == 1]
        for supps in itertools.product(subsets, repeat=k):
            # variables: c_t (interior), a_{θ,t} (t in supp θ), v_θ, lam (if interior)
            idx = {}
            for t in interior: idx[('c', t)] = len(idx)
            for th, S in enumerate(supps):
                for t in S: idx[('a', th, t)] = len(idx)
            for th in range(k): idx[('v', th)] = len(idx)
            if interior: idx['lam'] = len(idx)
            nv = len(idx); A, b = [], []
            def row(): return [F(0)] * nv
            # sum c = r
            R = row(); const = sum(1 for s in status if s == 2)
            for t in interior: R[idx[('c', t)]] = F(1)
            A.append(R); b.append(F(r - const))
            # attacker indifference on support: (1-c)u0 + c u1 = v  (linear in c)
            for th, (p, ap) in enumerate(types):
                for t in supps[th]:
                    R = row(); u0, u1 = ap[t]
                    if status[t] == 1:
                        R[idx[('c', t)]] = u1 - u0; rhs = -u0
                    else:
                        rhs = -(u1 if status[t] == 2 else u0)
                    R[idx[('v', th)]] = F(-1); A.append(R); b.append(rhs)
                R = row()
                for t in supps[th]: R[idx[('a', th, t)]] = F(1)
                A.append(R); b.append(F(1))
            # defender indifference among interior targets: gain_t = lam
            for t in interior:
                R = row(); d = dpay[t][1] - dpay[t][0]
                for th, (p, _) in enumerate(types):
                    if t in supps[th]: R[idx[('a', th, t)]] = p * d
                R[idx['lam']] = F(-1); A.append(R); b.append(F(0))
            x = solve_linear(A, b)
            if x is None: continue
            cov = [F(0) if s == 0 else F(1) if s == 2 else x[idx[('c', t)]]
                   for t, s in enumerate(status)]
            rows = [[x[idx[('a', th, t)]] if t in supps[th] else F(0) for t in range(n)]
                    for th in range(k)]
            if check_bne(r, dpay, types, cov, rows):
                found.append((tuple(cov), tuple(map(tuple, rows))))
    return found

def rand_game(rng, n, k, B=5):
    def pair(defender):
        a, b = rng.randint(-B, B), rng.randint(-B, B)
        lo, hi = min(a, b), max(a, b)
        return (F(lo), F(hi)) if defender else (F(hi), F(lo))
    w = [rng.randint(0 if B == 5 else 1, 3 if B == 5 else B) for _ in range(k)]
    if sum(w) == 0: w[0] = 1
    pri = [F(x, sum(w)) for x in w]
    r = rng.randint(0, n)
    return r, [pair(True) for _ in range(n)], [(pri[i], [pair(False) for _ in range(n)]) for i in range(k)]

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    B = int(sys.argv[3]) if len(sys.argv) > 3 else 5  # B>5: generic mode, positive priors
    rng = random.Random(seed)
    nofound = 0; multi_cov = 0; nonint = 0
    for i in range(N):
        n = rng.randint(1, 4); k = rng.randint(1, 2 if n == 4 else 3)
        g = rand_game(rng, n, k, B)
        eqs = equilibria(*g)
        covs = {e[0] for e in eqs}
        bad = [(e1, e2) for e1 in eqs for e2 in eqs
               if not check_bne(g[0], g[1], g[2], list(e1[0]), [list(x) for x in e2[1]])]
        if bad:
            nonint += 1; print('INTERCHANGEABILITY FAILS (positive priors=%s)' % all(p > 0 for p, _ in g[2]), g, bad[0])
        if not eqs: nofound += 1; print('NO BASIC EQUILIBRIUM FOUND', g)
        if len(covs) > 1: multi_cov += 1; print('multiple coverages', g, covs)
        if i < 5: print('game', g, '\n  eq', eqs[0] if eqs else None)
    print(f'games={N} without_found_eq={nofound} with_distinct_defender_coverages={multi_cov} non_interchangeable_pairs_games={nonint}')
