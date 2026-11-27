/* Independent brute force from Lean defs: CompleteProfile n: rank i : Perm (Fin n), rank i i = n-1.
   partnerRank = rank+1. Matching = involution. k-block (i,j): i!=j, mu i != j,
   pr i j + k <= pr i (mu i), pr j i + k <= pr j (mu j).
   For each N, enumerate ALL profiles (no normalization), compute per profile threshold
   t(p) = least k>=1 with a k-stable matching; report histogram and max = K(N). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int N; int inv[1000][8]; int ninv=0;
int perms[200][8]; int np=0; /* zero-based rank of candidates excluding self handled per agent */
void geninv(int *cur){ int i; for(i=0;i<N&&cur[i]>=0;i++); if(i==N){memcpy(inv[ninv++],cur,sizeof(int)*8);return;}
  cur[i]=i; geninv(cur); cur[i]=-1;
  for(int j=i+1;j<N;j++) if(cur[j]<0){cur[i]=j;cur[j]=i;geninv(cur);cur[i]=-1;cur[j]=-1;} }
/* rank tables: R[i][j] partnerRank */
int R[8][8];
/* list of rank-permutations for agent i: all perms sigma of Fin N with sigma(i)=N-1 */
int plist[8][800][8]; int pc[8];
void genperm(int i,int pos,int *used,int *sig){ if(pos==N){memcpy(plist[i][pc[i]++],sig,sizeof(int)*8);return;}
  if(pos==i){sig[i]=N-1; genperm(i,pos+1,used,sig); return;}
  for(int r=0;r<N-1;r++) if(!used[r]){used[r]=1;sig[pos]=r;genperm(i,pos+1,used,sig);used[r]=0;} }
int stable_exists(int k){
  for(int m=0;m<ninv;m++){ int *mu=inv[m]; int ok=1;
    for(int i=0;i<N&&ok;i++) for(int j=0;j<N;j++){ if(i==j||mu[i]==j) continue;
      if(R[i][j]+k<=R[i][mu[i]] && R[j][i]+k<=R[j][mu[j]]){ok=0;break;} }
    if(ok) return 1; }
  return 0; }
long hist[10]; long cnt;
void rec(int i){ if(i==N){ int k=1; while(!stable_exists(k)) k++; hist[k]++; cnt++; return; }
  for(int a=0;a<pc[i];a++){ for(int j=0;j<N;j++) R[i][j]=plist[i][a][j]+1; rec(i+1);} }
int main(int argc,char**argv){ N=atoi(argv[1]); int cur[8]; for(int i=0;i<8;i++)cur[i]=-1; geninv(cur);
  for(int i=0;i<N;i++){int used[8]={0},sig[8]; pc[i]=0; genperm(i,0,used,sig);}
  rec(0); printf("N=%d involutions=%d profiles=%ld\n",N,ninv,cnt);
  int K=0; for(int k=1;k<10;k++) if(hist[k]){printf(" threshold %d: %ld profiles\n",k,hist[k]); K=k;}
  printf(" K(%d)=%d\n",N,K); }
