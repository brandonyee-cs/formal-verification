/*
 * Exact first and second moments of the number S of stable matchings
 * (firm-covering injections Fin n -> Fin m) under independent uniform
 * complete strict preferences, matching StableMarriage.Unbalanced in
 * formal-conjectures.
 *
 * Method: condition on the firms' rankings F.  Given F and an injection mu,
 *  - an unmatched worker j blocks with firm i iff firm i ranks j above mu(i)
 *    (deterministic in F);
 *  - a matched worker j = mu(i0) blocks with i iff firm i ranks j above mu(i)
 *    (i in B_j) and worker j ranks i above i0.
 * Workers' rankings are independent, so P(mu, nu both stable | F) is a
 * product over workers of (#perms of Fin n meeting worker j's constraints)/n!.
 * Firm 0's ranking is fixed to the identity (relabelling workers), and the
 * rankings of firms 1..n-1 are enumerated as a multiset (relabelling firms
 * 1..n-1) with multinomial weights.  All sums are exact integers (__int128).
 *
 * Output: n m N1 N2 D, where E[S] = N1/D and E[S^2] = N2/D.
 * Usage: ./moments n m
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 5
#define MAXM 8
typedef __int128 i128;

static int n, m;
static int nperm_m;
static unsigned char (*permsM)[MAXM]; /* rank arrays: permsM[p][j] = rank of worker j */
static int permsN[120][MAXN], nperm_n;
static long long cnt[MAXN + 1][1 << MAXN][MAXN + 1][1 << MAXN];

static int rk[MAXN][MAXM];
static int inj[4096][MAXN];
static int ninj;
static int feas[4096], nfeas;
/* per feasible injection, per worker: (a, A) constraint, a == n means none */
static int ca[4096][MAXM], cA[4096][MAXM];

static void gen_perms(int k, int *arr, int used, int len, void (*emit)(int *)) {
  if (k == len) { emit(arr); return; }
  for (int v = 0; v < len; v++)
    if (!(used >> v & 1)) { arr[k] = v; gen_perms(k + 1, arr, used | 1 << v, len, emit); }
}
static int permsM_count = 0;
static void emitM(int *a) { for (int j = 0; j < m; j++) permsM[permsM_count][j] = (unsigned char)a[j]; permsM_count++; }
static void emitN(int *a) { for (int j = 0; j < n; j++) permsN[nperm_n][j] = a[j]; nperm_n++; }

static void gen_inj(int k, int *arr, int used) {
  if (k == n) { memcpy(inj[ninj++], arr, sizeof(int) * MAXN); return; }
  for (int v = 0; v < m; v++)
    if (!(used >> v & 1)) { arr[k] = v; gen_inj(k + 1, arr, used | 1 << v); }
}

static i128 S1, S2;

static void process(long long weight) {
  nfeas = 0;
  for (int t = 0; t < ninj; t++) {
    int *mu = inj[t];
    int matched = 0, owner[MAXM];
    for (int j = 0; j < m; j++) owner[j] = -1;
    for (int i = 0; i < n; i++) { matched |= 1 << mu[i]; owner[mu[i]] = i; }
    int ok = 1;
    for (int j = 0; j < m && ok; j++) {
      if (matched >> j & 1) continue;
      for (int i = 0; i < n; i++) if (rk[i][j] < rk[i][mu[i]]) { ok = 0; break; }
    }
    if (!ok) continue;
    int f = nfeas++;
    feas[f] = t;
    for (int j = 0; j < m; j++) {
      if (owner[j] < 0) { ca[f][j] = n; cA[f][j] = 0; continue; }
      int A = 0;
      for (int i = 0; i < n; i++) if (i != owner[j] && rk[i][j] < rk[i][mu[i]]) A |= 1 << i;
      ca[f][j] = owner[j]; cA[f][j] = A;
    }
  }
  i128 s1 = 0, s2 = 0;
  for (int f = 0; f < nfeas; f++) {
    i128 p = 1;
    for (int j = 0; j < m; j++) p *= cnt[ca[f][j]][cA[f][j]][n][0];
    s1 += p;
    for (int g = 0; g < nfeas; g++) {
      i128 q = 1;
      for (int j = 0; j < m; j++) q *= cnt[ca[f][j]][cA[f][j]][ca[g][j]][cA[g][j]];
      s2 += q;
    }
  }
  S1 += s1 * weight;
  S2 += s2 * weight;
}

static long long fact(int k) { long long r = 1; for (int i = 2; i <= k; i++) r *= i; return r; }

static int idx[MAXN];
static void rec(int k, int start) {
  if (k == n) {
    /* multinomial weight: (n-1)! / prod(multiplicities!) */
    long long w = fact(n - 1);
    int run = 1;
    for (int i = 2; i < n; i++) {
      if (idx[i] == idx[i - 1]) run++; else { w /= fact(run); run = 1; }
    }
    if (n >= 2) w /= fact(run);
    process(w);
    return;
  }
  for (int p = start; p < nperm_m; p++) {
    idx[k] = p;
    for (int j = 0; j < m; j++) rk[k][j] = permsM[p][j];
    rec(k + 1, p);
  }
}

static void print128(i128 x) {
  char buf[64]; int len = 0;
  if (x == 0) { printf("0"); return; }
  while (x > 0) { buf[len++] = '0' + (int)(x % 10); x /= 10; }
  while (len) putchar(buf[--len]);
}

int main(int argc, char **argv) {
  if (argc < 3) return 1;
  n = atoi(argv[1]); m = atoi(argv[2]);
  if (n < 1 || n > MAXN || m < n || m > MAXM) { fprintf(stderr, "bad args\n"); return 1; }
  nperm_m = (int)fact(m);
  permsM = malloc(sizeof(*permsM) * nperm_m);
  int arr[MAXM];
  gen_perms(0, arr, 0, m, emitM);
  nperm_n = 0;
  gen_perms(0, arr, 0, n, emitN);
  /* cnt[a][A][b][B]: # rank arrays r of Fin n (r[i] = rank of firm i) with
     r[a] < r[i] for i in A, and r[b] < r[i] for i in B; a == n means none. */
  for (int a = 0; a <= n; a++) for (int A = 0; A < 1 << n; A++)
    for (int b = 0; b <= n; b++) for (int B = 0; B < 1 << n; B++) {
      long long c = 0;
      for (int p = 0; p < nperm_n; p++) {
        int *r = permsN[p], ok = 1;
        for (int i = 0; i < n && ok; i++) {
          if (a < n && (A >> i & 1) && !(r[a] < r[i])) ok = 0;
          if (b < n && (B >> i & 1) && !(r[b] < r[i])) ok = 0;
        }
        c += ok;
      }
      cnt[a][A][b][B] = c;
    }
  int tmp[MAXN];
  ninj = 0;
  gen_inj(0, tmp, 0);
  /* firm 0 ranks workers by identity */
  for (int j = 0; j < m; j++) rk[0][j] = j;
  S1 = S2 = 0;
  rec(1, 0);
  i128 D = 1;
  for (int k = 1; k < n; k++) D *= nperm_m;
  for (int j = 0; j < m; j++) D *= fact(n);
  printf("%d %d ", n, m); print128(S1); printf(" "); print128(S2); printf(" "); print128(D); printf("\n");
  return 0;
}
