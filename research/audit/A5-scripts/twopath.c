/* Decide whether a simple graph's edge set partitions into at most two
   vertex-simple paths.  Input: one graph per line: n m u1 v1 ... um vm.
   Output: one line per graph: 1 (yes) or 0 (no). m <= 63, n <= 64. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int n, m, eu[64], ev[64], adjn[64], adjv[64][64], adje[64][64];
static u64 inc[64], ALL;
static int found;
static int complement_is_path(u64 R){
  if(!R) return 1;
  int deg1=0, start=-1;
  for(int v=0; v<n; v++){ int d=__builtin_popcountll(R&inc[v]); if(d>2) return 0; if(d==1){ deg1++; start=v; } }
  if(deg1!=2) return 0;
  /* walk the path from start; it must use every edge of R (no extra cycles) */
  int cnt=0, u=start; u64 left=R;
  while(1){
    u64 e = left & inc[u];
    if(!e) break;
    int i = __builtin_ctzll(e);
    left &= ~(1ULL<<i); cnt++;
    u = (eu[i]==u)? ev[i] : eu[i];
  }
  return left==0;
}
static void dfs(int u, u64 vis, u64 used){
  if(found) return;
  for(int i=0;i<adjn[u];i++){
    int w=adjv[u][i]; if(vis>>w&1) continue;
    u64 nu = used | (1ULL<<adje[u][i]);
    if(complement_is_path(ALL & ~nu)){ found=1; return; }
    dfs(w, vis|(1ULL<<w), nu);
    if(found) return;
  }
}
int main(void){
  while(scanf("%d %d",&n,&m)==2){
    memset(adjn,0,sizeof adjn); memset(inc,0,sizeof inc);
    for(int i=0;i<m;i++){ scanf("%d %d",&eu[i],&ev[i]); int a=eu[i],b=ev[i];
      adjv[a][adjn[a]]=b; adje[a][adjn[a]++]=i; adjv[b][adjn[b]]=a; adje[b][adjn[b]++]=i;
      inc[a]|=1ULL<<i; inc[b]|=1ULL<<i; }
    ALL = (m==64)?~0ULL:((1ULL<<m)-1);
    found=0;
    if(m==0) found=1;
    int odd=0; for(int v=0;v<n;v++) if(adjn[v]%2) odd++;
    for(int s=0;s<n && !found;s++){
      if(odd && adjn[s]%2==0) continue;
      if(!adjn[s]) continue;
      dfs(s, 1ULL<<s, 0);
    }
    printf("%d\n", found); fflush(stdout);
  }
  return 0;
}
