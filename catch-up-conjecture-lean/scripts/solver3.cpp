// Threshold search with a LOSSY fixed-size transposition table (cache only; correctness does
// not depend on it). Decides value(Icc 1 N) via ge(draw) and ge(win), same semantics as
// solver2.cpp and Lean `ge` in lean/CatchUpEval.lean.
// Usage: solver3 lo hi log2_table_entries
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <ctime>
int N; uint64_t *tab; uint64_t mask_;
static inline uint64_t h(uint64_t k){k^=k>>33;k*=0xff51afd7ed558ccdULL;k^=k>>33;k*=0xc4ceb9fe1a85ec53ULL;k^=k>>33;return k;}
// ge(w,m,g): mover behind by g>=0 (non-first). w=1: value==win ; w=0: value!=loss
bool ge(int w, uint64_t m, int g, int sum){
  if(m==0) return w? false : g==0;
  if(sum<g) return false;
  uint64_t key=((m<<10|g)<<1|w)+1, i=h(key)&mask_;
  uint64_t e=tab[i]; if((e>>1)==key) return e&1;
  bool res=false;
  for(int x=1;x<=N && !res;x++) if(m>>(x-1)&1){
    uint64_t m2=m&~(1ULL<<(x-1));
    if(x>=g) res=!ge(!w,m2,x-g,sum-x); else res=ge(w,m2,g-x,sum-x);
  }
  tab[i]=(key<<1)|res; return res;}
int main(int argc,char**argv){
  int lo=atoi(argv[1]),hi=atoi(argv[2]); uint64_t cap=1ULL<<atoi(argv[3]); mask_=cap-1;
  tab=(uint64_t*)calloc(cap,8);
  for(N=lo;N<=hi;N++){ if(getenv("EVEN_ONLY") && (N*(N+1)/2)%2) continue; memset(tab,0,cap*8); time_t t0=time(0);
    uint64_t m=(1ULL<<N)-1; int sum=N*(N+1)/2;
    // first move: P1 takes x, P2 behind by x. P1 >= draw iff exists x with !ge(win) for P2 ...
    bool d=false,w=false;
    for(int x=1;x<=N&&!d;x++) d=!ge(1,m&~(1ULL<<(x-1)),x,sum-x);
    for(int x=1;x<=N&&!w;x++) w=!ge(0,m&~(1ULL<<(x-1)),x,sum-x);
    const char*s=w?"win":(d?"draw":"loss");
    printf("N=%d T=%d value=%s %s secs=%ld\n",N,sum,s,(sum%2==0)?(!w&&d?"CONJ_OK":"COUNTEREXAMPLE"):"",(long)(time(0)-t0));
    fflush(stdout);}
}
