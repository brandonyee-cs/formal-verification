# Test simple move rules: at every reachable state, is the rule's move value-optimal?
import sys
from functools import lru_cache
sys.setrecursionlimit(100000)
@lru_cache(None)
def V(l, g, first):  # l: frozenset remaining, g = deficit of current player (opp - me), may be <0 only... ; returns -1/0/1
    if not l: return (g<0)-(g>0)
    if sum(l)<g: return -1
    return max(child(l,g,first,x) for x in l)
def child(l,g,first,x):
    l2=l-{x}
    if first or x>=g: return -V(l2, x-g, False)
    return V(l2, g-x, False)
rules={
 'max': lambda l,g,f: max(l),
 'min': lambda l,g,f: min(l),
 'min_catch_else_max': lambda l,g,f: min([x for x in l if x>=g], default=max(l)),
 'max_noncatch_else_mincatch': lambda l,g,f: max([x for x in l if x<g], default=min(l)),
 'exact_tie_else_max': lambda l,g,f: g if g in l else max(l),
 'exact_tie_else_min': lambda l,g,f: g if g in l else min(l),
}
for N in range(3,int(sys.argv[1])+1):
    V.cache_clear()
    S=frozenset(range(1,N+1))
    # enumerate reachable states (all moves)
    seen=set(); stack=[(S,0,True)]; stats={r:[0,0] for r in rules}
    while stack:
        st=stack.pop()
        if st in seen: continue
        seen.add(st); l,g,f=st
        if not l or sum(l)<g: continue
        v=V(l,g,f)
        for r,fn in rules.items():
            x=fn(l,g,f); stats[r][0]+=1
            if child(l,g,f,x)==v: stats[r][1]+=1
        for x in l:
            l2=l-{x}
            stack.append((l2,x-g,False) if (f or x>=g) else (l2,g-x,False))
    print(N, V(S,0,True), {r:f'{s[1]}/{s[0]}' for r,s in stats.items()}, flush=True)
