// Count nodes of the unmemoized threshold evaluator `ge` (as in lean/CatchUpEval.lean)
// under different move orderings. Usage: treecount N order
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
using namespace std;
int ORD; long long cnt;
vector<int> order(const vector<int>& l,int a,int b,bool f){
  vector<int> o=l; int g=b-a; // deficit (may be <=0 only at first move)
  switch(ORD){
   case 0: sort(o.begin(),o.end()); break;
   case 1: sort(o.begin(),o.end(),greater<int>()); break;
   case 2: // ending moves (x>=g) first ascending, then continuing moves descending
     stable_sort(o.begin(),o.end(),[&](int x,int y){bool ex=x>=g,ey=y>=g; if(ex!=ey) return ex; return ex? x<y : x>y;}); break;
   case 3: // ending moves first ascending, then continuing ascending
     stable_sort(o.begin(),o.end(),[&](int x,int y){bool ex=x>=g,ey=y>=g; if(ex!=ey) return ex; return x<y;}); break;
   case 4: // continuing moves first descending, then ending ascending
     stable_sort(o.begin(),o.end(),[&](int x,int y){bool ex=x>=g,ey=y>=g; if(ex!=ey) return ey; return ex? x<y : x>y;}); break;
   case 5: // continuing ascending, then ending ascending
     stable_sort(o.begin(),o.end(),[&](int x,int y){bool ex=x>=g,ey=y>=g; if(ex!=ey) return ey; return x<y;}); break;
  }
  return o;}
bool ge(bool w, const vector<int>& l, int a, int b, bool f){
  cnt++;
  if(l.empty()) return w? b<a : b<=a;
  int s=0; for(int x:l) s+=x; if(a+s<b) return false;
  for(int x: order(l,a,b,f)){
    vector<int> l2; for(int y:l) if(y!=x) l2.push_back(y);
    bool ok;
    if(f || b<=a+x) ok=!ge(!w,l2,b,a+x,false); else ok=ge(w,l2,a+x,b,false);
    if(ok) return true;
  }
  return false;}
int main(int argc,char**argv){int N=atoi(argv[1]); ORD=atoi(argv[2]);
  vector<int> l; for(int i=1;i<=N;i++) l.push_back(i);
  cnt=0; bool d=ge(false,l,0,0,true); long long c1=cnt; cnt=0; bool w=ge(true,l,0,0,true);
  printf("N=%d ord=%d ge_draw=%d ge_win=%d nodes=%lld %lld total=%lld\n",N,ORD,d,w,c1,cnt,c1+cnt);}
