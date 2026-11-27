// Emit a minimal-ish claim certificate for value(Icc 1 N) = draw.
// Claims: (mask, g, w, v) meaning thr_w(D(list(mask), g)) = v, where
//   thr_true(o) = (o == win), thr_false(o) = (o != loss), D = mover behind by g (non-first).
// Positive claims need one witness child (first in ascending order); negative claims need all
// children. Root claims: (full, 0, false, true) and (full, 0, true, false)  [g=0 models first move].
// Output: count, and optionally the sorted keys: key = ((mask*1024 + g)*2 + w)*2 + v.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <algorithm>
using namespace std;
int N;
unordered_map<uint64_t,bool> memo;
bool ge(int w, uint64_t m, int g, int sum){
  if(m==0) return w? false : g==0;
  if(sum<g) return false;
  uint64_t key=(m<<10|g)<<1|w;
  auto it=memo.find(key); if(it!=memo.end()) return it->second;
  bool res=false;
  for(int x=1;x<=N && !res;x++) if(m>>(x-1)&1){
    uint64_t m2=m&~(1ULL<<(x-1));
    if(x>=g) res=!ge(!w,m2,x-g,sum-x); else res=ge(w,m2,g-x,sum-x);
  }
  memo[key]=res; return res;}
unordered_set<uint64_t> cert; vector<uint64_t> out;
void need(int w, uint64_t m, int g, int sum){
  bool v=ge(w,m,g,sum);
  uint64_t k=((m<<10|g)<<1|w);
  if(cert.count(k)) return; cert.insert(k); out.push_back(k<<1|v);
  if(m==0 || sum<g) return;
  for(int x=1;x<=N;x++) if(m>>(x-1)&1){
    uint64_t m2=m&~(1ULL<<(x-1)); bool ok; int w2,g2;
    if(x>=g){ w2=!w; g2=x-g; ok=!ge(w2,m2,g2,sum-x);} else { w2=w; g2=g-x; ok=ge(w2,m2,g2,sum-x);}
    if(v){ if(ok){ need(w2,m2,g2,sum-x); return; } }
    else need(w2,m2,g2,sum-x);
  }
}
int main(int argc,char**argv){N=atoi(argv[1]); uint64_t m=(1ULL<<N)-1; int s=N*(N+1)/2;
  bool a=ge(0,m,0,s), b=ge(1,m,0,s);
  need(0,m,0,s); need(1,m,0,s);
  fprintf(stderr,"N=%d ge_draw=%d ge_win=%d certsize=%zu memo=%zu\n",N,a,b,out.size(),memo.size());
  if(argc>2){ sort(out.begin(),out.end()); FILE*f=fopen(argv[2],"w"); for(auto k:out) fprintf(f,"%llu\n",(unsigned long long)k); fclose(f);} }
