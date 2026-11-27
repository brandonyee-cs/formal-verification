# Node count of the unmemoized threshold evaluator ge(t, state) (t in {draw=0, win=1}):
#   ge(t,s) = exists child c: (swap c -> not ge(t+1-?...))  -- see Lean file CatchUpEval.lean
import sys
sys.setrecursionlimit(10000)
def run(N, order):
    cnt=[0]
    # ge(t,l,a,b,first): value >= t  (t=0 draw, t=1 win), current player perspective
    def ge(t,l,a,b,first):
        cnt[0]+=1
        if not l: return (a>b)-(a<b) >= t
        if a+sum(l)<b: return False
        for x in l:
            l2=tuple(y for y in l if y!=x); a2=a+x
            if first or a2>=b:
                # my value of child = -(opp value); need -(v)>=t  <=> v <= -t <=> not (v >= -t+1)
                ok = not ge(1-t,l2,b,a2,False) if t==0 else not ge(0,l2,b,a2,False)
            else: ok = ge(t,l2,a2,b,False)
            if ok: return True
        return False
    l=tuple(order(N)); d=ge(0,l,0,0,True); c1=cnt[0]; cnt[0]=0; w=ge(1,l,0,0,True); c2=cnt[0]
    return d,w,c1,c2
for N in range(int(sys.argv[2]) if len(sys.argv)>2 else 1,int(sys.argv[1])+1):
    print(N, 'asc',run(N, lambda n: range(1,n+1)), flush=True)
