from functools import lru_cache
from itertools import combinations
# Independent: a turn = choose a set X of remaining such that some ordering keeps strictly behind
# until last pick; equivalently sum(X)-max(X) < gap <= sum(X) ... (with max last); or take all if can't catch up.
@lru_cache(None)
def val(rem, me, opp):  # rem frozenset, returns +1/0/-1 for mover; mover is to start a non-first turn
    if not rem: return (me>opp)-(me<opp)
    gap = opp-me
    if sum(rem) < gap: return -1
    best=-2; r=sorted(rem)
    for k in range(1,len(r)+1):
        for X in combinations(r,k):
            s=sum(X)
            if s>=gap and (k==1 or s-max(X)<gap):
                v=-val(rem-frozenset(X), opp, me+s); best=max(best,v)
    return best
def value(N):
    S=frozenset(range(1,N+1))
    return max(-val(S-{x},0,x) for x in S) if S else 0
for N in range(0,13): print(N, N*(N+1)//2%2==0, value(N))
