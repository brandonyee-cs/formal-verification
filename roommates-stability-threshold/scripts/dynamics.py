"""Experiment: for N = 2m+1, try to construct an m-stable matching by
  M1 (mutual first choices) + maximal matching in H = {ij : mutually within top m+1},
  then repeatedly repair defects (single s, matched j at rank m+1, f(j)=s, r_s(j)<=m+1) by swapping.
Reports whether the dynamics ever cycles (step cap) and verifies final m-stability exactly."""
import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kstable import ranks

def run(prefs, m, rng, cap=10000):
    N = len(prefs); R = ranks(prefs); t = m + 1
    f = [p[0] for p in prefs]
    mu = list(range(N))
    for i in range(N):
        if f[f[i]] == i: mu[i] = f[i]
    def extend():
        singles = [i for i in range(N) if mu[i] == i]; rng.shuffle(singles)
        for a in singles:
            if mu[a] != a: continue
            for b in singles:
                if b != a and mu[b] == b and R[a][b] <= t and R[b][a] <= t:
                    mu[a] = b; mu[b] = a; break
    extend()
    for step in range(cap):
        defects = [(s, j) for j in range(N) if mu[j] != j and R[j][mu[j]] == t
                   for s in [f[j]] if mu[s] == s and R[s][j] <= t]
        if not defects: break
        s, j = rng.choice(defects); a = mu[j]
        mu[a] = a; mu[s] = j; mu[j] = s
        extend()
    else:
        return None
    # exact m-stability check
    for i in range(N):
        for j in range(i+1, N):
            if mu[i] != j and R[i][j] + m <= R[i][mu[i]] and R[j][i] + m <= R[j][mu[j]]:
                raise Exception("not m-stable! %s %s" % (prefs, mu))
    return step

if __name__ == "__main__":
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    N = int(sys.argv[1]); m = (N - 1) // 2
    worst = 0
    for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 2000):
        # biased random profiles: many agents share popular top choices (adversarial-ish)
        prefs = []
        for i in range(N):
            others = [j for j in range(N) if j != i]
            w = {j: rng.random() * (1 + 3 * (j < 3)) for j in others} if trial % 2 else {j: rng.random() for j in others}
            prefs.append(sorted(others, key=lambda j: -w[j]))
        st = run(prefs, m, rng)
        if st is None: print("CYCLE/CAP", prefs); break
        worst = max(worst, st)
    print("N=%d m=%d trials ok, max repair steps=%d" % (N, m, worst))
