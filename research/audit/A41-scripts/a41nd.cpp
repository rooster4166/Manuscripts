// a41nd.cpp -- independent order-11 census for audit A41.
// Reads graph6 graphs B (all 2-connected graphs of order 10 from geng -C 10), forms J = B + z with
// z joined to the even vertices of B, keeps J if delta(J) >= 3, z is its only even vertex, and J is
// 3-connected; then for every r in N(z) without matching data writes "T1 g6(J) z r def d twins t",
// and prints a census on stderr (graphs, roots, no-data roots, deficiency and twin counts).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned int u32;
static int N; static u32 A[17];
static bool read_g6(const char *s) {
  N = (unsigned char)s[0] - 63; if (N < 1 || N > 16) return false;
  int k = 1, bit = 0, cur = 0;
  for (int v = 0; v < N; v++) A[v] = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    if (bit == 0) { cur = (unsigned char)s[k++] - 63; bit = 6; }
    bit--;
    if (cur >> bit & 1) { A[i] |= 1u << j; A[j] |= 1u << i; }
  }
  return true;
}
static string to_g6() {
  string s; s += (char)(63 + N);
  int bit = 0, cur = 0;
  for (int j = 1; j < N; j++) for (int i = 0; i < j; i++) {
    cur = (cur << 1) | (A[i] >> j & 1); bit++;
    if (bit == 6) { s += (char)(63 + cur); bit = 0; cur = 0; }
  }
  if (bit) { cur <<= (6 - bit); s += (char)(63 + cur); }
  return s;
}
static bool conn(u32 S) {
  if (!S) return true;
  u32 c = S & -S, fr = c;
  while (fr) { int x = __builtin_ctz(fr); fr &= fr - 1; u32 nb = A[x] & S & ~c; c |= nb; fr |= nb; }
  return c == S;
}
static bool three_conn() {
  u32 all = (1u << N) - 1;
  if (N < 4 || !conn(all)) return false;
  for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++) if (!conn(all & ~(1u << a) & ~(1u << b))) return false;
  return true;
}
static bool pm(u32 S) {
  if (!S) return true;
  int a = __builtin_ctz(S); u32 S2 = S & ~(1u << a);
  for (u32 nb = A[a] & S2; nb; nb &= nb - 1) { int b = __builtin_ctz(nb); if (pm(S2 & ~(1u << b))) return true; }
  return false;
}
static int nu(u32 S) {
  if (!S) return 0;
  int a = __builtin_ctz(S); u32 S2 = S & ~(1u << a);
  int best = nu(S2);
  for (u32 nb = A[a] & S2; nb; nb &= nb - 1) { int b = __builtin_ctz(nb); best = max(best, 1 + nu(S2 & ~(1u << b))); }
  return best;
}
int main() {
  char line[256];
  long long graphs = 0, roots = 0, nod = 0; map<int, long long> def; long long tw = 0;
  map<int, long long> dzc;
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\r\n")] = 0;
    if (!line[0] || !read_g6(line)) continue;
    int z = N; A[z] = 0;
    for (int v = 0; v < N; v++) if (!(__builtin_popcount(A[v]) & 1)) { A[v] |= 1u << z; A[z] |= 1u << v; }
    N++;
    int mind = 99, nev = 0;
    for (int v = 0; v < N; v++) { int d = __builtin_popcount(A[v]); mind = min(mind, d); if (!(d & 1)) nev++; }
    if (mind < 3 || nev != 1 || !three_conn()) continue;
    graphs++;
    u32 T = A[z]; int dz = __builtin_popcount(T);
    roots += dz;
    if (pm(T)) continue;
    int df = dz - 2 * nu(T);
    string g = to_g6();
    for (u32 rl = T; rl; rl &= rl - 1) {
      int r = __builtin_ctz(rl);
      int twins = 0;
      for (int a = 0; a < N; a++) for (int b = a + 1; b < N; b++)
        if ((T >> a & 1) && (T >> b & 1) && __builtin_popcount(A[a]) == 3 && A[a] == A[b]) twins = 1;
      nod++; def[df]++; tw += twins; dzc[dz]++;
      printf("T1 %s %d %d def %d dz %d twins %d\n", g.c_str(), z, r, df, dz, twins);
    }
  }
  fprintf(stderr, "CENSUS graphs=%lld roots=%lld nodata=%lld twins=%lld\n", graphs, roots, nod, tw);
  for (auto &kv : def) fprintf(stderr, "def %d: %lld\n", kv.first, kv.second);
  for (auto &kv : dzc) fprintf(stderr, "dz %d: %lld\n", kv.first, kv.second);
}
