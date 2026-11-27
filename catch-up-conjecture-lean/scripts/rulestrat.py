# Does a fixed simple rule, used by one player against an optimal opponent, secure >= draw?
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
sys.path.insert(0,'.')
rules={
 'max': lambda l,g: max(l),
 'min': lambda l,g: min(l),
 'min_catch_else_max': lambda l,g: min([x for x in l if x>=g], default=max(l)),
 'max_noncatch_else_mincatch': lambda l,g: max([x for x in l if x<g], default=min(l)),
 'exact_tie_else_min': lambda l,g: g if g in l else min(l),
 'exact_tie_else_max': lambda l,g: g if g in l else max(l),
 'min_noncatch_else_mincatch': lambda l,g: min(l),
}
def solve(N, rule, rplayer, firstmove):
    @lru_cache(None)
    def V(l, g, first, who):  # value for player `who` to move (0=P1,1=P2), from P1 perspective
        if not l: return (g<0)-(g>0) if who==0 else -((g<0)-(g>0))
        if sum(l)<g: return -1 if who==0 else 1
        if who==rplayer:
            xs=[firstmove] if (first and firstmove) else [rule(l,g)]
        else: xs=l
        vals=[]
        for x in xs:
            l2=l-{x}
            if first or x>=g: vals.append(V(l2,x-g,False,1-who))
            else: vals.append(V(l2,g-x,False,who))
        return max(vals) if who==0 else min(vals)
    return V(frozenset(range(1,N+1)),0,True,0)
for N in [3,4,7,8,11,12,15,16]:
    out=[]
    for r,fn in rules.items():
        # P1 using rule (try every first move), P2 using rule
        p1=max(solve(N,fn,0,x) for x in range(1,N+1))
        p2=solve(N,fn,1,None)
        out.append(f'{r}:P1>={p1},P2gets{-p2}')
    print(N,' '.join(out),flush=True)
