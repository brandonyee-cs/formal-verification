"""CNF: does a complete roommates profile on N agents exist with NO k-stable matching?
Conventions = Roommates.lean (rank 1..N-1 partners, N = single, partial matchings, both gain >= k).
SAT  <=> stabilityThreshold N > k.   Symmetry breaking: agent 0's list is 1 > 2 > ... > N-1 (WLOG).
Usage: python3 satgen.py N k out.cnf [nobreak]"""
import sys, itertools

def involutions(N):
    res = []
    def rec(cur):
        try: i = cur.index(-1)
        except ValueError: res.append(tuple(cur)); return
        cur[i] = i; rec(cur); cur[i] = -1
        for j in range(i+1, N):
            if cur[j] == -1:
                cur[i] = j; cur[j] = i; rec(cur); cur[i] = -1; cur[j] = -1
    rec([-1]*N); return res

def build(N, k, symbreak=True, matchings=True):
    nv = [0]; cls = []
    def new():
        nv[0] += 1; return nv[0]
    R = range(1, N)  # positions
    x = {(i, j, r): new() for i in range(N) for j in range(N) if j != i for r in R}
    for i in range(N):
        for j in range(N):
            if j == i: continue
            cls.append([x[i, j, r] for r in R])
            for r, s in itertools.combinations(R, 2): cls.append([-x[i, j, r], -x[i, j, s]])
        for r in R:
            cls.append([x[i, j, r] for j in range(N) if j != i])
            for a, b in itertools.combinations([j for j in range(N) if j != i], 2):
                cls.append([-x[i, a, r], -x[i, b, r]])
    # le[i,j,t] -> rank_i(j) <= t
    le = {}
    for i in range(N):
        for j in range(N):
            if j == i: continue
            for t in R:
                v = new(); le[i, j, t] = v
                cls.append([-v] + [x[i, j, s] for s in range(1, t+1)])
    FALSE = new(); cls.append([-FALSE])
    def LE(i, j, t):
        if t <= 0: return FALSE
        if t >= N-1: return None  # always true
        return le[i, j, t]
    # g[i,j,m] -> rank_i(j) + k <= rank_i(m)   (m = partner of i, m == i means single, rank N)
    g = {}
    for i in range(N):
        for j in range(N):
            if j == i: continue
            for m in range(N):
                if m == j: continue
                v = new(); g[i, j, m] = v
                if m == i:
                    l = LE(i, j, N - k)
                    if l is not None: cls.append([-v, l])
                else:
                    for r in R:
                        l = LE(i, j, r - k)
                        if l is not None: cls.append([-v, -x[i, m, r], l])
    p = {}
    def P(i, j, m, mm):
        key = (i, j, m, mm)
        if key not in p:
            v = new(); p[key] = v
            cls.append([-v, g[i, j, m]]); cls.append([-v, g[j, i, mm]])
        return p[key]
    for mu in (involutions(N) if matchings else []):
        cls.append([P(i, j, mu[i], mu[j]) for i in range(N) for j in range(i+1, N) if mu[i] != j])
    if symbreak:
        for r in R: cls.append([x[0, r, r]])
    return nv[0], cls, x

if __name__ == "__main__":
    N, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    nvars, cls, x = build(N, k, symbreak=(len(sys.argv) < 5))
    with open(out, "w") as f:
        f.write("p cnf %d %d\n" % (nvars, len(cls)))
        for c in cls: f.write(" ".join(map(str, c)) + " 0\n")
    # variable map for decoding
    with open(out + ".map", "w") as f:
        for (i, j, r), v in x.items(): f.write("%d %d %d %d\n" % (v, i, j, r))
