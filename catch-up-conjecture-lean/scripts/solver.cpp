// Exact solver for Catch-Up({1..N}) mirroring CatchUp.valueAux in the Lean file.
// State: remaining mask, d = s_me - s_opp (scores are integers; only the difference matters
// for every branch of valueAux: comparisons s_me>s_opp, s_me+sum<s_opp, s_me+x>=s_opp).
// Outcome encoding: 1 win, 0 draw, -1 loss (from the current player's view).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <unordered_map>
#include <vector>
using namespace std;
int N; vector<int> vals;
unordered_map<uint64_t,int8_t> memo;
static int sumMask(uint64_t m){int s=0;for(int i=0;i<N;i++) if(m>>i&1) s+=vals[i];return s;}
int V(uint64_t m, long d, int sum){ // not first move
  if(m==0) return d>0?1:(d<0?-1:0);
  if(d+sum<0) return -1;
  uint64_t key=(m<<20)^(uint64_t)(d+(1<<19));
  auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int best=-1;
  // order: try large numbers first (heuristic only; result is max over all moves)
  for(int i=N-1;i>=0 && best<1;i--) if(m>>i&1){
    int x=vals[i]; uint64_t m2=m&~(1ULL<<i); long d2=d+x; int r;
    if(d2>=0) r=-V(m2,-d2,sum-x); else r=V(m2,d2,sum-x);
    if(r>best) best=r;
  }
  memo[key]=best; return best;
}
int value(){ uint64_t m=(N==64)?~0ULL:((1ULL<<N)-1); int sum=sumMask(m);
  if(m==0) return 0;
  int best=-1;
  for(int i=0;i<N;i++){int x=vals[i]; int r=-V(m&~(1ULL<<i),-(long)x,sum-x); if(r>best) best=r;}
  return best;}
int main(int argc,char**argv){
  int lo=atoi(argv[1]),hi=atoi(argv[2]);
  for(N=lo;N<=hi;N++){ vals.clear(); for(int i=1;i<=N;i++) vals.push_back(i); memo.clear();
    int v=value(); long T=(long)N*(N+1)/2;
    const char* s=v==1?"win":(v==0?"draw":"loss");
    printf("N=%d T=%ld T_even=%d value=%s states=%zu %s\n",N,T,(int)(T%2==0),s,memo.size(),
      (T%2==0)?(v==0?"CONJ_OK":"COUNTEREXAMPLE"):"");
    fflush(stdout);}
}
