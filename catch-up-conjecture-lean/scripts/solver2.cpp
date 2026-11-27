// Memory-lean exact solver for Catch-Up({1..N}); same semantics as solver.cpp / Lean valueAux.
// Open-addressing table: entry = key | (value+1)<<62, key = mask<<10 | (-d) (d<=0 in all non-first states).
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
using namespace std;
int N; uint64_t *tab; uint64_t cap, cnt=0;
static inline uint64_t h(uint64_t k){k^=k>>33;k*=0xff51afd7ed558ccdULL;k^=k>>33;k*=0xc4ceb9fe1a85ec53ULL;k^=k>>33;return k;}
int V(uint64_t m, int g, int sum){ // current player behind by g>=0 (d=-g), not first move
  if(m==0) return g>0?-1:0;
  if(sum<g) return -1;
  uint64_t key=(m<<10)|g, i=h(key)&(cap-1);
  while(tab[i]){ if((tab[i]&((1ULL<<62)-1))==key) return (int)(tab[i]>>62)-1; i=(i+1)&(cap-1);}
  int best=-1;
  for(int x=N;x>=1 && best<1;x--) if(m>>(x-1)&1){
    uint64_t m2=m&~(1ULL<<(x-1)); int r;
    if(x>=g) r=-V(m2,x-g,sum-x); else r=V(m2,g-x,sum-x);
    if(r>best) best=r;
  }
  // re-probe (table may have changed during recursion)
  i=h(key)&(cap-1); while(tab[i]) i=(i+1)&(cap-1);
  tab[i]=key|((uint64_t)(best+1)<<62); cnt++;
  if(cnt*10>cap*8){fprintf(stderr,"table full\n");exit(1);}
  return best;}
int main(int argc,char**argv){
  int lo=atoi(argv[1]),hi=atoi(argv[2]); int lg=atoi(argv[3]); cap=1ULL<<lg;
  tab=(uint64_t*)calloc(cap,8);
  for(N=lo;N<=hi;N++){ memset(tab,0,cap*8); cnt=0;
    uint64_t m=(1ULL<<N)-1; int sum=N*(N+1)/2, best=-1;
    if(N==0) best=0;
    for(int x=1;x<=N;x++){int r=-V(m&~(1ULL<<(x-1)),x,sum-x); if(r>best) best=r;}
    const char* s=best==1?"win":(best==0?"draw":"loss");
    printf("N=%d T=%d T_even=%d value=%s states=%lu %s\n",N,sum,(int)(sum%2==0),s,(unsigned long)cnt,
      (sum%2==0)?(best==0?"CONJ_OK":"COUNTEREXAMPLE"):""); fflush(stdout);}
}
