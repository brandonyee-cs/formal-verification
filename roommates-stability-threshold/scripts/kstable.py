"""Exact (integer) helpers: does a complete roommates profile admit a k-stable matching?
Conventions = Lean file Roommates.lean: rank 1..N-1 for partners, rank N for being single,
partial matchings allowed, (i,j) k-blocks mu iff mu(i)!=j and both gain >= k positions."""
import itertools, sys

def ranks(prefs):
    N = len(prefs)
    R = [[0]*N for _ in range(N)]
    for i, L in enumerate(prefs):
        assert sorted(L) == [j for j in range(N) if j != i]
        for r, j in enumerate(L):
            R[i][j] = r + 1
        R[i][i] = N
    return R

def kstable_matching(R, k):
    """Return a k-stable matching (partner list) or None. DFS with pruning on decided agents."""
    N = len(R)
    mu = [-1]*N
    order = []
    def blocks(i, j):
        return mu[i] != j and R[i][j] + k <= R[i][mu[i]] and R[j][i] + k <= R[j][mu[j]]
    def ok_new(a):
        for b in order:
            if b != a and blocks(a, b):
                return False
        return True
    def rec():
        try:
            i = mu.index(-1)
        except ValueError:
            return True
        cands = [i] + sorted((j for j in range(N) if j != i and mu[j] == -1), key=lambda j: R[i][j])
        for j in cands:
            mu[i] = j; mu[j] = i
            new = [i] if j == i else [i, j]
            good = True
            for a in new:
                order.append(a)
            for a in new:
                if not ok_new(a):
                    good = False; break
            if good and rec():
                return True
            for a in new:
                order.pop()
            mu[i] = -1; mu[j] = -1
        return False
    return list(mu) if rec() else None

def threshold(R):
    """least k>=1 such that a k-stable matching exists"""
    k = 1
    while kstable_matching(R, k) is None:
        k += 1
    return k

if __name__ == "__main__":
    # circulant profiles: agent i ranks i+d_1, i+d_2, ... (mod N)
    N = int(sys.argv[1]); k = int(sys.argv[2])
    cnt = 0
    for ds in itertools.permutations(range(1, N)):
        prefs = [[(i+d) % N for d in ds] for i in range(N)]
        R = ranks(prefs)
        if kstable_matching(R, k) is None:
            cnt += 1
            if cnt <= 10: print("no %d-stable circulant:" % k, ds)
    print("N=%d k=%d circulant profiles without k-stable matching: %d" % (N, k, cnt))
