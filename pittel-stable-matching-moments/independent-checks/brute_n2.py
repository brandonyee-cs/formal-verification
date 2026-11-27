# Independent brute force written by a separate reviewing (Claude) session, not by the session
# that wrote the Lean proofs; shares no code with scripts/. For n = 2 firms and m = 2..5 workers it
# enumerates all profiles, computes S literally from the upstream blocking condition, compares
# E[S], E[S^2] with 1 + 1/(4m(m-1)), 1 + 3/(4m(m-1)), and checks S = (2 if C else 1) per profile.
# Usage: python3 -I brute_n2.py
from itertools import permutations, product
from fractions import Fraction
import sys
n=2
def run(m):
    perms_m=list(permutations(range(m)))  # firmRank i : worker -> rank
    perms_n=list(permutations(range(n)))  # workerRank j : firm -> rank
    matchings=[mu for mu in product(range(m),repeat=n) if len(set(mu))==n]
    tot=0; s1=0; s2=0; mismatch=0
    for fr in product(perms_m,repeat=n):
        inv=[[0]*m for _ in range(n)]
        for i in range(n):
            for w in range(m): inv[i][fr[i][w]]=w
        for wr in product(perms_n,repeat=m):
            cnt=0
            for mu in matchings:
                stable=True
                for i in range(n):
                    for j in range(m):
                        if mu[i]!=j and fr[i][j]<fr[i][mu[i]] and all(wr[j][i]<wr[j][k] for k in range(n) if mu[k]==j):
                            stable=False;break
                    if not stable:break
                cnt+=stable
            tot+=1; s1+=cnt; s2+=cnt*cnt
            prefB=lambda w: wr[w][1]<wr[w][0]
            a0,a1,b0,b1=inv[0][0],inv[0][1],inv[1][0],inv[1][1]
            C= a0==b1 and b0==a1 and prefB(a0) and not prefB(b0)
            if cnt!=(2 if C else 1): mismatch+=1
    E=Fraction(s1,tot);E2=Fraction(s2,tot)
    f1=1+Fraction(1,4*m*(m-1)); f2=1+Fraction(3,4*m*(m-1))
    print(m,tot,E,E2,E==f1,E2==f2,"mismatch",mismatch,flush=True)
for m in range(2,6): run(m)
