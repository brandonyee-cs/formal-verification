// Exhaustive search for complete roommates profiles with NO k-stable matching.
// Conventions exactly as in FormalConjecturesForMathlib/Combinatorics/Roommates.lean:
//   agents 0..N-1, rank_i(j) in 1..N-1 for j != i (1 = best), rank_i(i) = N (single);
//   matchings = all involutions (partial matchings allowed);
//   (i,j) k-blocks mu iff i != j, mu(i) != j, rank_i(j)+k <= rank_i(mu i), rank_j(i)+k <= rank_j(mu j).
// Agent 0's list is fixed to 1>2>...>N-1 (WLOG by relabelling agents 1..N-1).
// Usage: ./search N k [stop_at_first(0/1)]
// Output: number of (agent-0-normalised) profiles with no k-stable matching; prints first few.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
#define W 4            // up to 256 matchings
typedef struct { uint64_t w[W]; } mask;

static int N, K, STOP, SH=0, NSH=1;
static int nperm;                  // (N-1)!
static int perms[5040][MAXN];      // perms[p][r] = r-th choice (agent offset index 0..N-2)
static int nmatch;
static int mt[1024][MAXN];         // partner arrays
static int rk[MAXN][5040][MAXN];   // rk[i][p][j] = rank of j for agent i under list p
static mask *kill;                 // kill[((i*N+j)*nperm + a)*nperm + b]
static int prof[MAXN];
static long long found = 0, leaves = 0;

static void gen_match(int *cur, int i) {
  while (i < N && cur[i] >= 0) i++;
  if (i == N) { memcpy(mt[nmatch++], cur, sizeof(int)*N); return; }
  cur[i] = i; gen_match(cur, i+1); cur[i] = -1;
  for (int j = i+1; j < N; j++) if (cur[j] < 0) {
    cur[i] = j; cur[j] = i; gen_match(cur, i+1); cur[i] = -1; cur[j] = -1;
  }
}

static int pp[MAXN], used[MAXN];
static void gen_perm(int d) {
  if (d == N-1) { memcpy(perms[nperm++], pp, sizeof(int)*(N-1)); return; }
  for (int x = 0; x < N-1; x++) if (!used[x]) { used[x]=1; pp[d]=x; gen_perm(d+1); used[x]=0; }
}

static void print_profile(void) {
  printf("PROFILE");
  for (int i = 0; i < N; i++) {
    printf(" |");
    for (int r = 0; r < N-1; r++) { int x = perms[prof[i]][r]; int j = x < i ? x : x+1; printf(" %d", j); }
  }
  printf("\n"); fflush(stdout);
}

static void dfs(int m, mask alive) {
  if (m == N) {
    leaves++;
    int z = 1; for (int t = 0; t < W; t++) if (alive.w[t]) z = 0;
    if (z) { found++; if (found <= 5) print_profile(); if (STOP) { printf("found=%lld\n", found); exit(0);} }
    return;
  }
  int start = 0, end = nperm;
  if (m == 0) end = 1;  // agent 0 fixed to identity order
  for (int a = start; a < end; a++) {
    if (m == 1 && a % NSH != SH) continue;
    prof[m] = a;
    mask al = alive;
    int z = 1;
    for (int i = 0; i < m; i++) {
      mask *km = &kill[((i*N+m)*nperm + prof[i])*nperm + a];
      for (int t = 0; t < W; t++) al.w[t] &= ~km->w[t];
    }
    for (int t = 0; t < W; t++) if (al.w[t]) z = 0;
    if (z) { // already no k-stable matching: every completion is a counterexample
      long long c = 1; for (int q = m+1; q < N; q++) c *= nperm;
      found += c; leaves += c;
      if (found - c < 5) {
        for (int q = m+1; q < N; q++) prof[q] = 0;
        print_profile();
      }
      if (STOP) { printf("found=%lld\n", found); exit(0);}
      continue;
    }
    dfs(m+1, al);
  }
}

int main(int argc, char **argv) {
  N = atoi(argv[1]); K = atoi(argv[2]); STOP = argc > 3 ? atoi(argv[3]) : 0;
  if (argc > 5) { SH = atoi(argv[4]); NSH = atoi(argv[5]); }
  int cur[MAXN]; for (int i = 0; i < N; i++) cur[i] = -1;
  gen_match(cur, 0);
  if (nmatch > 64*W) { fprintf(stderr, "too many matchings\n"); return 1; }
  gen_perm(0);
  for (int i = 0; i < N; i++) for (int p = 0; p < nperm; p++) {
    for (int r = 0; r < N-1; r++) { int x = perms[p][r]; int j = x < i ? x : x+1; rk[i][p][j] = r+1; }
    rk[i][p][i] = N;
  }
  kill = calloc((size_t)N*N*nperm*nperm, sizeof(mask));
  for (int i = 0; i < N; i++) for (int j = i+1; j < N; j++)
    for (int a = 0; a < nperm; a++) for (int b = 0; b < nperm; b++) {
      mask *km = &kill[((i*N+j)*nperm + a)*nperm + b];
      for (int u = 0; u < nmatch; u++) {
        if (mt[u][i] == j) continue;
        if (rk[i][a][j] + K <= rk[i][a][mt[u][i]] && rk[j][b][i] + K <= rk[j][b][mt[u][j]])
          km->w[u/64] |= 1ULL << (u%64);
      }
    }
  mask all; memset(&all, 0, sizeof all);
  for (int u = 0; u < nmatch; u++) all.w[u/64] |= 1ULL << (u%64);
  dfs(0, all);
  printf("N=%d k=%d matchings=%d leaves=%lld no_k_stable_profiles=%lld\n", N, K, nmatch, leaves, found);
  return 0;
}
