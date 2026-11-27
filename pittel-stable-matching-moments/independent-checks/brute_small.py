# Independent brute force written by a separate reviewing (Claude) session, not by the session
# that wrote the Lean proofs; shares no code with scripts/. Prints n m #profiles sum(S) sum(S^2)
# E[S] E[S^2] for (2,2), (2,3), (3,2), (3,3), computed literally from the upstream blocking condition.
# Usage: python3 -I brute_small.py
from itertools import permutations, product
from fractions import Fraction
def run(n,m):
    fp=list(permutations(range(m))); wp=list(permutations(range(n)))
    inj=[f for f in product(range(m),repeat=n) if len(set(f))==n]
    S1=S2=N=0
    for fr in product(fp,repeat=n):
      for wr in product(wp,repeat=m):
        c=0
        for mu in inj:
          ok=True
          for i in range(n):
            for j in range(m):
              if mu[i]!=j and fr[i][j]<fr[i][mu[i]] and all(wr[j][i]<wr[j][k] for k in range(n) if mu[k]==j):
                ok=False
          c+=ok
        S1+=c;S2+=c*c;N+=1
    print(n,m,N,S1,S2,Fraction(S1,N),Fraction(S2,N))
run(2,2);run(2,3);run(3,2);run(3,3)
