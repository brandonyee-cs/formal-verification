// Simulated annealing hunting for complete roommates profiles on N agents with NO k-stable matching.
// Same conventions as Roommates.lean (rank 1..N-1, single = N, partial matchings, both gain >= k).
// cost(profile) = min over all matchings mu of #k-blocking pairs of mu  (we MAXIMISE; >0 = witness).
// Usage: ./anneal N k seed iters
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXN 12
static int N, K;
static int nm; static signed char (*mt)[MAXN];
static int pref[MAXN][MAXN]; // pref[i][r] = agent at position r (0-based), r < N-1
static int R[MAXN][MAXN];

static void gen(signed char *cur, int i) {
  while (i < N && cur[i] >= 0) i++;
  if (i == N) { memcpy(mt[nm++], cur, MAXN); return; }
  cur[i] = i; gen(cur, i+1); cur[i] = -1;
  for (int j = i+1; j < N; j++) if (cur[j] < 0) { cur[i]=j; cur[j]=i; gen(cur,i+1); cur[i]=-1; cur[j]=-1; }
}
static long long count_inv(int n){ long long a=1,b=1; for(int m=2;m<=n;m++){ long long c=b+(m-1)*a; a=b;b=c;} return n==0?1:b; }

static void mkR(void){ for(int i=0;i<N;i++){ for(int r=0;r<N-1;r++) R[i][pref[i][r]]=r+1; R[i][i]=N; } }
static int minb; // min over mu of max blocking strength b(mu)
static double cost(void){
  mkR();
  double best = 1e18; minb = 1<<30;
  for (int u=0; u<nm; u++){
    signed char *m = mt[u]; int b=0; double s=0;
    for (int i=0;i<N;i++){ int gi0 = R[i][(int)m[i]];
      for (int j=i+1;j<N;j++){ if (m[i]==j) continue;
        int gi = gi0 - R[i][j], gj = R[j][(int)m[j]] - R[j][i];
        int g = gi<gj?gi:gj; if (g>0){ s += g*g; if (g>b) b=g; } } }
    double sc = b*1000.0 + s;
    if (sc < best) best = sc;
    if (b < minb) minb = b;
  }
  return best;
}
static double rnd(void){ return rand()/(RAND_MAX+1.0); }
int main(int argc, char**argv){
  N=atoi(argv[1]); K=atoi(argv[2]); srand(atoi(argv[3])); long iters=atol(argv[4]);
  mt = malloc(count_inv(N)*MAXN); signed char cur[MAXN]; memset(cur,-1,MAXN); gen(cur,0);
  for(int i=0;i<N;i++){ int r=0; for(int j=0;j<N;j++) if(j!=i) pref[i][r++]=j;
    for(int r2=N-2;r2>0;r2--){ int s=rand()%(r2+1); int t=pref[i][r2]; pref[i][r2]=pref[i][s]; pref[i][s]=t; } }
  double c = cost(), bestc = c; double T = 1.0;
  for (long it=0; it<iters; it++){
    int i=rand()%N, a=rand()%(N-1), b=rand()%(N-1); if(a==b) continue;
    int t=pref[i][a]; pref[i][a]=pref[i][b]; pref[i][b]=t;
    double c2=cost(); int mb=minb;
    if (c2 >= c || rnd() < exp((c2-c)/(T*30))) { c=c2; } else { t=pref[i][a]; pref[i][a]=pref[i][b]; pref[i][b]=t; }
    T = 1.0*(1.0 - (double)it/iters) + 0.05;
    if (c > bestc) bestc = c;
    if (c2 == c && mb >= K) {
      printf("FOUND N=%d k=%d minb=%d it=%ld PROFILE", N, K, mb, it);
      for(int x=0;x<N;x++){ printf(" |"); for(int r=0;r<N-1;r++) printf(" %d",pref[x][r]); }
      printf("\n"); return 0;
    }
  }
  printf("none N=%d k=%d best=%.0f\n", N, K, bestc); return 0;
}
