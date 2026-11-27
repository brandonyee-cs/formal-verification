"""SAT test of the structural claim behind a possible general bound K(2m+1) <= m:
  F(p) = { matchings mu : every matched pair is mutually within top t, every mutual-first-choice pair
           is matched, no two singles are mutually within top t }    (t = m+1 by default)
CLAIM: some mu in F(p) is k-stable (k = m).   SAT <=> a profile violating the claim exists.
Usage: python3 satfamily.py N k t [timeout]"""
import sys, os, subprocess, itertools, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import satgen, kstable

def build(N, k, t, symbreak=True):
    nv, cls, x = satgen.build(N, k, symbreak, matchings=False)
    # recover le vars: satgen allocates le right after x in order; rebuild exact definitions instead
    cnt = [nv]
    def new():
        cnt[0] += 1; return cnt[0]
    R = range(1, N)
    LE = {}
    for i in range(N):
        for j in range(N):
            if j == i: continue
            for tt in R:
                v = new(); LE[i, j, tt] = v
                cls.append([-v] + [x[i, j, s] for s in range(1, tt+1)])
                for s in range(1, tt+1): cls.append([-x[i, j, s], v])
    def le(i, j, tt):
        return None if tt >= N-1 else LE[i, j, tt]   # None = always true
    # reuse satgen blocking structure by regenerating p-literals: simpler to redo here
    g = {}
    def G(i, j, m):
        key = (i, j, m)
        if key in g: return g[key]
        v = new(); g[key] = v
        if m == i:
            l = le(i, j, N - k) if N - k >= 1 else None
            if N - k <= 0: cls.append([-v])
            elif l is not None: cls.append([-v, l])
        else:
            for r in R:
                if r - k <= 0: cls.append([-v, -x[i, m, r]])
                else:
                    l = le(i, j, r - k)
                    if l is not None: cls.append([-v, -x[i, m, r], l])
        return v
    def P(i, j, m, mm):
        v = new(); cls.append([-v, G(i, j, m)]); cls.append([-v, G(j, i, mm)]); return v
    memoP = {}
    def Pm(*a):
        if a not in memoP: memoP[a] = P(*a)
        return memoP[a]
    mf = {}
    def MF(a, b):  # a,b mutual first choices
        if (a, b) not in mf:
            v = new(); mf[a, b] = v
            cls.append([-v, x[a, b, 1]]); cls.append([-v, x[b, a, 1]])
        return mf[a, b]
    hh = {}
    def HH(a, b):  # a,b mutually within top t
        if (a, b) not in hh:
            v = new(); hh[a, b] = v
            for l in (le(a, b, t), le(b, a, t)):
                if l is not None: cls.append([-v, l])
        return hh[a, b]
    for mu in satgen.involutions(N):
        c = []
        for i in range(N):
            j = mu[i]
            if j > i:
                for l in (le(i, j, t), le(j, i, t)):
                    if l is not None: c.append(-l)   # pair outside H -> mu not in F
        for a in range(N):
            for b in range(a+1, N):
                if mu[a] != b:
                    c.append(MF(a, b))
                    if mu[a] == a and mu[b] == b: c.append(HH(a, b))
                    c.append(Pm(a, b, mu[a], mu[b]))
        cls.append(c)
    return cnt[0], cls, x

if __name__ == "__main__":
    N, k, t = map(int, sys.argv[1:4]); to = int(sys.argv[4]) if len(sys.argv) > 4 else 3600
    nv, cls, x = build(N, k, t)
    here = os.path.dirname(os.path.abspath(__file__))
    cnf = os.path.join(here, "..", "logs", "family_N%d_k%d_t%d.cnf" % (N, k, t))
    with open(cnf, "w") as f:
        f.write("p cnf %d %d\n" % (nv, len(cls)))
        for c in cls: f.write(" ".join(map(str, c)) + " 0\n")
    t0 = time.time()
    r = subprocess.run([os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical"), "-q", "-t", str(to), cnf], capture_output=True, text=True)
    st = [l for l in r.stdout.splitlines() if l.startswith("s ")]
    print("family N=%d k=%d t=%d status=%s time=%.1fs" % (N, k, t, st, time.time() - t0))
    if st and st[0] == "s SATISFIABLE":
        true = set()
        for l in r.stdout.splitlines():
            if l.startswith("v "): true.update(int(a) for a in l.split()[1:] if int(a) > 0)
        prefs = [[None]*(N-1) for _ in range(N)]
        for (i, j, rr), v in x.items():
            if v in true: prefs[i][rr-1] = j
        print("PROFILE", prefs)
        print("threshold of this profile:", kstable.threshold(kstable.ranks(prefs)))
    os.remove(cnf)
