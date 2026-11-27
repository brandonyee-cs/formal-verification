"""Independent encoding (pairwise-order variables, no symmetry breaking).
SAT iff exists complete profile on N agents with no k-stable matching (Lean semantics)."""
import sys, itertools
N,k,out=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
nv=0; cls=[]
def new():
    global nv; nv+=1; return nv
P={}
for i in range(N):
    oth=[a for a in range(N) if a!=i]
    for a,b in itertools.combinations(oth,2):
        v=new(); P[i,a,b]=v; P[i,b,a]=-v   # P[i,a,b]: i strictly prefers a to b
    for a,b,c in itertools.permutations(oth,3):
        cls.append([-P[i,a,b],-P[i,b,c],P[i,a,c]])
T=new(); cls.append([T])
def pref(i,a,b):  # literal: a >=_i b  (a==b -> true)
    return T if a==b else P[i,a,b]
G={}
def gain(i,j,m):
    """literal g with g -> gain of i from m to j is >= k.  gain = pr(m)-pr(j).
    m==i: pr(m)=N, gain = 1 + #{a!=i,j: j >_i a}.  else gain = #{a!=i: j >_i a and a >=_i m}."""
    if (i,j,m) in G: return G[i,j,m]
    g=new(); G[i,j,m]=g
    oth=[a for a in range(N) if a!=i and a!=j]
    z=[]
    for a in oth:
        za=new(); z.append(za)
        cls.append([-za,P[i,j,a]])
        if m!=i: cls.append([-za,pref(i,a,m)])
    need = k-1 if m==i else k
    if need>len(z): cls.append([-g])
    elif need>0:
        for Tset in itertools.combinations(z,len(z)-need+1):
            cls.append([-g]+list(Tset))
    return g
def invs(N):
    res=[]
    def rec(cur):
        if -1 not in cur: res.append(tuple(cur)); return
        i=cur.index(-1); cur[i]=i; rec(cur); cur[i]=-1
        for j in range(i+1,N):
            if cur[j]==-1: cur[i]=j;cur[j]=i;rec(cur);cur[i]=-1;cur[j]=-1
    rec([-1]*N); return res
for mu in invs(N):
    cl=[]
    for i in range(N):
        for j in range(N):
            if i==j or mu[i]==j: continue
            b=new(); cls.append([-b,gain(i,j,mu[i])]); cls.append([-b,gain(j,i,mu[j])]); cl.append(b)
    cls.append(cl)
with open(out,'w') as f:
    f.write("p cnf %d %d\n"%(nv,len(cls)))
    for c in cls: f.write(" ".join(map(str,c))+" 0\n")
