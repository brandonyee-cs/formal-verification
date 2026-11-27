# Count nodes visited by a lazy, unmemoized evaluation of the list evaluator `ev`
# (short-circuits Outcome.best once a win is found), for a given list order.
import sys
from functools import lru_cache
sys.setrecursionlimit(10000)
def run(N, order):
    cnt=[0]
    def ev(l, a, b, first):
        cnt[0]+=1
        if not l: return (a>b)-(a<b)
        if a+sum(l)<b: return -1
        best=-1
        for x in l:
            l2=tuple(y for y in l if y!=x); a2=a+x
            if first or a2>=b: r=-ev(l2,b,a2,False)
            else: r=ev(l2,a2,b,False)
            best=max(best,r)
            if best==1: break
        return best
    v=ev(tuple(order(N)),0,0,True); return v,cnt[0]
for N in range(1,int(sys.argv[1])+1):
    print(N, run(N, lambda n: range(1,n+1)), run(N, lambda n: range(n,0,-1)), flush=True)
