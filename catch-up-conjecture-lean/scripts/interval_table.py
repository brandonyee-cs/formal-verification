# Value table V({1..k}, g) for non-first positions: mover behind by g with remaining {1..k}.
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
@lru_cache(None)
def V(l, g):
    if not l: return (g<0)-(g>0)
    if sum(l)<g: return -1
    best=-1
    for x in sorted(l):
        l2=l-{x}
        r=-V(l2,x-g) if x>=g else V(l2,g-x)
        if r>best: best=r
        if best==1: break
    return best
K=int(sys.argv[1])
for k in range(1,K+1):
    T=k*(k+1)//2
    row=''.join({1:'W',0:'D',-1:'L'}[V(frozenset(range(1,k+1)),g)] for g in range(0,T+1))
    print(f'k={k:2d} T={T:3d} parityT={T%2}', row, flush=True)
