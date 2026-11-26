/* Exact "p(G) <= budget?" for small simple graphs (n<=16, m<=64), DFS over paths with memo. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
static int pn_n, pn_m; static int pn_eu[64], pn_ev[64]; static u64 pn_inc[16]; static int pn_eid[16][16];
static long pn_nodes, pn_limit=50000000;
static int pn_aborted;
#define HBITS 20
static u64 *hkey; static signed char *hval; static unsigned *hstamp; static unsigned curstamp=1;
static void pn_init_hash(void){ if(!hkey){ hkey=malloc(sizeof(u64)<<HBITS); hval=malloc(1<<HBITS); hstamp=calloc(1<<HBITS,sizeof(unsigned)); } curstamp++; }
static int hget(u64 k){ u64 h=(k*0x9E3779B97F4A7C15ULL)>>(64-HBITS); for(int i=0;i<16;i++){ u64 j=(h+i)&((1<<HBITS)-1); if(hstamp[j]!=curstamp) return -1; if(hkey[j]==k) return hval[j]; } return -1; }
static void hput(u64 k,int v){ u64 h=(k*0x9E3779B97F4A7C15ULL)>>(64-HBITS); for(int i=0;i<16;i++){ u64 j=(h+i)&((1<<HBITS)-1); if(hstamp[j]!=curstamp){ hstamp[j]=curstamp; hkey[j]=k; hval[j]=v; return; } if(hkey[j]==k){ if(hval[j]<v) hval[j]=v; return; } } }
static void pn_setgraph(int n, int adj[16][16]){
  pn_n=n; pn_m=0; for(int i=0;i<n;i++) pn_inc[i]=0;
  for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(adj[i][j]){ pn_eu[pn_m]=i; pn_ev[pn_m]=j; pn_eid[i][j]=pn_eid[j][i]=pn_m; pn_inc[i]|=1ULL<<pn_m; pn_inc[j]|=1ULL<<pn_m; pn_m++; }
}
static int feas(u64 R,int rem);
/* enumerate paths from v (start) inside R; post-order (longer first); for each path try feas(R\P, rem-1) */
static int pathdfs(u64 R,int rem,int cur,int vis,u64 used,int start, int mustedge){
  /* extend first */
  u64 out = R & pn_inc[cur] & ~used;
  for(u64 m=out;m;m&=m-1){ int e=__builtin_ctzll(m); int w = pn_eu[e]==cur?pn_ev[e]:pn_eu[e]; if(vis>>w&1) continue;
    if(pathdfs(R,rem,w,vis|(1<<w),used|(1ULL<<e),start,mustedge)) return 1; if(pn_aborted) return 0; }
  if(used && (mustedge<0 || (used>>mustedge&1))) { if(feas(R&~used,rem-1)) return 1; }
  return 0;
}
static int feas(u64 R,int rem){
  if(!R) return 1; if(rem<=0) return 0;
  if(++pn_nodes>pn_limit){ pn_aborted=1; return 0; }
  int odd=0, vodd=-1, dodd=99, vmin=-1, dmin=99, dmax=0;
  for(int v=0;v<pn_n;v++){ int d=__builtin_popcountll(R&pn_inc[v]); if(!d) continue; if(d>dmax) dmax=d;
    if(d&1){ odd++; if(d<dodd){dodd=d;vodd=v;} } if(d<dmin){dmin=d;vmin=v;} }
  int lb = odd/2; if((dmax+1)/2>lb) lb=(dmax+1)/2; if(lb<1) lb=1;
  if(lb>rem) return 0;
  int hv=hget(R); if(hv>=rem) return 0;
  int ok=0;
  if(vodd>=0){ ok=pathdfs(R,rem,vodd,1<<vodd,0,vodd,-1); }
  else {
    /* all even: path containing a fixed edge e at vmin: enumerate as path from vmin starting with e? No: e may be interior.
       Enumerate paths through e: first walk forward from w (other end) then backward from vmin. Simpler: any path containing e
       is a path starting at some vertex; we enumerate paths starting at every vertex that contain e. Use: start at each vertex s. */
    u64 em = R & pn_inc[vmin]; int e = __builtin_ctzll(em);
    for(int s=0;s<pn_n && !ok && !pn_aborted;s++) if(R&pn_inc[s]) ok=pathdfs(R,rem,s,1<<s,0,s,e);
  }
  if(!ok && !pn_aborted) hput(R,rem);
  return ok;
}
/* returns 1 feasible, 0 infeasible, -1 aborted */
static int pn_le(int budget){ pn_init_hash(); pn_nodes=0; pn_aborted=0; u64 all = (pn_m==64)?~0ULL:((1ULL<<pn_m)-1); int r=feas(all,budget); if(pn_aborted) return -1; return r; }
/* graph6 decode */
static int g6decode(const char*s,int adj[16][16]){
  int n=s[0]-63; int k=0; int bit=0; const char*p=s+1; int val=0;
  memset(adj,0,sizeof(int)*16*16);
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(bit==0){ val=*p-63; p++; bit=6; } bit--; if((val>>bit)&1){ adj[i][j]=adj[j][i]=1; } k++; }
  return n;
}
