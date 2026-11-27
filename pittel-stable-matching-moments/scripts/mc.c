/*
 * Monte Carlo (NOT exact; supplementary evidence only) for the number S of stable
 * matchings with n firms and m >= n workers, uniform independent preferences.
 * Enumerates all stable matchings: firm-proposing deferred acceptance gives the
 * firm-optimal matching; then BFS over break-marriage moves (McVitie-Wilson /
 * Gusfield-Irving), with dedup by a hash set. Every matching found is
 * re-checked for stability. Mode "check" compares with brute force over all
 * injections on small random instances.
 * Usage: ./mc n m samples seed        -> n m samples mean(S) mean(S^2) ratio se_ratio
 *        ./mc n m samples seed hist  -> also prints every sampled S value
 *        (followed by raw sums of S, S^2, S^3, S^4 for pooling)
 *        ./mc check n m trials seed
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static int n, m;
static int *fp, *frank, *wr; /* fp[i*m+r], frank[i*m+j], wr[j*n+i] */
static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void shuffle(int *a, int k) { for (int i = k - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; } }

static void gen(void) {
  for (int i = 0; i < n; i++) {
    int *p = fp + i * m;
    for (int r = 0; r < m; r++) p[r] = r;
    shuffle(p, m);
    for (int r = 0; r < m; r++) frank[i * m + p[r]] = r;
  }
  int tmp[4096];
  for (int j = 0; j < m; j++) {
    for (int r = 0; r < n; r++) tmp[r] = r;
    shuffle(tmp, n);
    for (int r = 0; r < n; r++) wr[j * n + tmp[r]] = r;
  }
}

static int is_stable(const int *mu) {
  static int owner[8192];
  for (int j = 0; j < m; j++) owner[j] = -1;
  for (int i = 0; i < n; i++) owner[mu[i]] = i;
  for (int i = 0; i < n; i++)
    for (int r = 0; r < frank[i * m + mu[i]]; r++) {
      int j = fp[i * m + r];
      if (owner[j] < 0 || wr[j * n + i] < wr[j * n + owner[j]]) return 0;
    }
  return 1;
}

/* storage of found matchings */
static int *store; static int nstore, capstore;
static uint64_t *htab; static int hcap;
static uint64_t hashm(const int *mu) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < n; i++) { h ^= (uint64_t)mu[i] + 1; h *= 1099511628211ULL; } return h | 1; }
static int *hidx;
static int *used_slots; static int nused;
static int insert(const int *mu) { /* returns 1 if new */
  uint64_t h = hashm(mu);
  int s = h & (hcap - 1);
  while (htab[s]) {
    if (htab[s] == h && memcmp(store + (size_t)hidx[s] * n, mu, sizeof(int) * n) == 0) return 0;
    s = (s + 1) & (hcap - 1);
  }
  if (nstore == capstore) { capstore *= 2; store = realloc(store, sizeof(int) * (size_t)capstore * n); }
  memcpy(store + (size_t)nstore * n, mu, sizeof(int) * n);
  htab[s] = h; hidx[s] = nstore++; used_slots[nused++] = s;
  if (nstore * 2 > hcap) { fprintf(stderr, "hash full\n"); exit(2); }
  return 1;
}

static int *M, *W, *pos;
static int breakm(const int *mu0, int i, int *out) {
  for (int j = 0; j < m; j++) W[j] = -1;
  for (int k = 0; k < n; k++) { M[k] = mu0[k]; W[mu0[k]] = k; pos[k] = frank[k * m + mu0[k]] + 1; }
  int w = M[i];
  W[w] = -2; /* temporarily free, accepts only firms better than i */
  int f = i;
  for (;;) {
    if (pos[f] >= m) return 0;
    int v = fp[f * m + pos[f]++];
    if (v == w) {
      if (wr[w * n + f] < wr[w * n + i]) { W[w] = f; M[f] = w; break; }
      continue;
    }
    if (W[v] == -1) return 0; /* would match a worker outside the matched set */
    int g = W[v];
    if (wr[v * n + f] < wr[v * n + g]) { W[v] = f; M[f] = v; f = g; pos[g] = frank[g * m + v] + 1; }
  }
  memcpy(out, M, sizeof(int) * n);
  return 1;
}

static long count_stable(void) {
  /* deferred acceptance, firms propose */
  for (int j = 0; j < m; j++) W[j] = -1;
  int *stack = malloc(sizeof(int) * n), top = 0;
  for (int i = 0; i < n; i++) { pos[i] = 0; stack[top++] = i; }
  while (top) {
    int f = stack[--top];
    for (;;) {
      int v = fp[f * m + pos[f]++];
      if (W[v] == -1) { W[v] = f; M[f] = v; break; }
      if (wr[v * n + f] < wr[v * n + W[v]]) { int g = W[v]; W[v] = f; M[f] = v; stack[top++] = g; break; }
    }
  }
  free(stack);
  int *mu0 = malloc(sizeof(int) * n), *nu = malloc(sizeof(int) * n);
  memcpy(mu0, M, sizeof(int) * n);
  for (int u = 0; u < nused; u++) htab[used_slots[u]] = 0;
  nused = 0;
  nstore = 0;
  insert(mu0);
  for (int q = 0; q < nstore; q++) {
    memcpy(mu0, store + (size_t)q * n, sizeof(int) * n);
    if (!is_stable(mu0)) { fprintf(stderr, "BUG: unstable matching found\n"); exit(3); }
    for (int i = 0; i < n; i++)
      if (breakm(mu0, i, nu)) insert(nu);
  }
  free(mu0); free(nu);
  return nstore;
}

static long brute_rec(int k, int *mu, int used) {
  if (k == n) return is_stable(mu);
  long c = 0;
  for (int v = 0; v < m; v++) if (!(used >> v & 1)) { mu[k] = v; c += brute_rec(k + 1, mu, used | 1 << v); }
  return c;
}

static void setup(void) {
  fp = malloc(sizeof(int) * n * m); frank = malloc(sizeof(int) * n * m); wr = malloc(sizeof(int) * n * m);
  M = malloc(sizeof(int) * n); W = malloc(sizeof(int) * m); pos = malloc(sizeof(int) * n);
  capstore = 1024; store = malloc(sizeof(int) * (size_t)capstore * n);
  hcap = 1 << 22; htab = malloc(sizeof(uint64_t) * hcap); hidx = malloc(sizeof(int) * hcap);
  memset(htab, 0, sizeof(uint64_t) * hcap); used_slots = malloc(sizeof(int) * hcap); nused = 0;
}

int main(int argc, char **argv) {
  if (argc >= 6 && strcmp(argv[1], "check") == 0) {
    n = atoi(argv[2]); m = atoi(argv[3]); long T = atol(argv[4]); rs = strtoull(argv[5], 0, 10) * 2654435761ULL + 1;
    setup();
    int mu[32];
    for (long t = 0; t < T; t++) {
      gen();
      long a = count_stable(), b = brute_rec(0, mu, 0);
      if (a != b) { printf("MISMATCH trial %ld: bfs %ld brute %ld\n", t, a, b); return 1; }
    }
    printf("check n=%d m=%d trials=%ld OK\n", n, m, T);
    return 0;
  }
  if (argc < 5) return 1;
  int hist = argc >= 6 && strcmp(argv[5], "hist") == 0; /* print each S value */
  n = atoi(argv[1]); m = atoi(argv[2]); long T = atol(argv[3]); rs = strtoull(argv[4], 0, 10) * 2654435761ULL + 1;
  setup();
  double s1 = 0, s2 = 0, s3 = 0, s4 = 0;
  for (long t = 0; t < T; t++) {
    gen();
    double S = (double)count_stable();
    if (hist) printf("S %ld\n", (long)S);
    s1 += S; s2 += S * S; s3 += S * S * S; s4 += S * S * S * S;
  }
  double a = s1 / T, b = s2 / T;
  /* delta-method standard error of b / a^2 */
  double c3 = s3 / T, c4 = s4 / T;
  double va = b - a * a, vb = c4 - b * b, cab = c3 - a * b;
  double ga = -2 * b / (a * a * a), gb = 1 / (a * a);
  double var = (ga * ga * va + gb * gb * vb + 2 * ga * gb * cab) / T;
  printf("%d %d %ld %.6f %.6f %.6f %.6f sums %.17g %.17g %.17g %.17g\n", n, m, T, a, b, b / (a * a), sqrt(var > 0 ? var : 0), s1, s2, s3, s4);
  return 0;
}
