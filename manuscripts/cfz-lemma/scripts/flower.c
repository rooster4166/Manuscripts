/* Exhaustive test of the short-path-and-cycles statement.
 *
 * Usage: flower n k q mode [xpos]
 *   vertices 0..n-1 of K_n; P = (0,1,...,k-1)
 *   mode 0: every cycle meets V(P)            (general form)
 *   mode 1: every cycle contains vertex xpos  (common-vertex form, xpos in 0..k-1)
 * Enumerates all q-sets of pairwise edge-disjoint cycles of K_n - E(P)
 * (cycles listed once, sets as increasing index tuples) and decides by
 * exact search whether E(P) u E(cycles) partitions into q+1 simple paths.
 * Prints every failure and summary counts.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
static int n, k, q, mode, xpos;
static int eid[16][16];
static int eu[128], ev[128];
static int ne;
static u64 *cyc; static int ncyc, capc;
static int *cycv; /* vertex lists, n+1 per cycle (first = length) */
static u64 Pmask;

static void addcycle(int *v, int L){
  u64 m=0; for(int i=0;i<L;i++){ m |= 1ULL<<eid[v[i]][v[(i+1)%L]]; }
  if(m & Pmask) return;
  if(mode==0){ int ok=0; for(int i=0;i<L;i++) if(v[i]<k) ok=1; if(!ok) return; }
  else { int ok=0; for(int i=0;i<L;i++) if(v[i]==xpos) ok=1; if(!ok) return; }
  if(ncyc==capc){ capc=capc?2*capc:1024; cyc=realloc(cyc,capc*sizeof(u64)); cycv=realloc(cycv,capc*(n+1)*sizeof(int)); }
  cyc[ncyc]=m; cycv[ncyc*(n+1)]=L; for(int i=0;i<L;i++) cycv[ncyc*(n+1)+1+i]=v[i];
  ncyc++;
}
/* generate cycles: smallest vertex first, second < last */
static int cv[16], used[16];
static void gen(int depth, int L){
  if(depth==L){ if(cv[1]<cv[L-1]) addcycle(cv,L); return; }
  for(int w=cv[0]+1; w<n; w++) if(!used[w]){ used[w]=1; cv[depth]=w; gen(depth+1,L); used[w]=0; }
}

/* adjacency within a mask */
static int adjl[16][16], adjc[16][16]; /* neighbor, edge id */
static int deg0[16];

static long long nodes;
static int search(u64 R, int t);
static int pathv[20], plen;

static int armR(u64 R, int t, u64 pathedges, int vis, int end){
  /* current full path = left arm (reversed) + u v + right arm ending at 'end' */
  /* option: stop here */
  nodes++;
  if(search(R & ~pathedges, t-1)) return 1;
  for(int i=0;i<deg0[end];i++){
    int w=adjl[end][i]; int e=adjc[end][i];
    if(!((R>>e)&1)) continue; if((pathedges>>e)&1) continue; if(vis>>w&1) continue;
    if(armR(R,t,pathedges|(1ULL<<e), vis|(1<<w), w)) return 1;
  }
  return 0;
}
static int armL(u64 R, int t, u64 pathedges, int vis, int end, int v){
  if(armR(R,t,pathedges,vis,v)) return 1;
  for(int i=0;i<deg0[end];i++){
    int w=adjl[end][i]; int e=adjc[end][i];
    if(!((R>>e)&1)) continue; if((pathedges>>e)&1) continue; if(vis>>w&1) continue;
    if(armL(R,t,pathedges|(1ULL<<e), vis|(1<<w), w, v)) return 1;
  }
  return 0;
}
static int search(u64 R, int t){
  if(!R) return 1;
  if(t==0) return 0;
  int cnt=__builtin_popcountll(R);
  if(cnt > t*(n-1)) return 0;
  /* odd degree count */
  int odd=0;
  for(int v=0;v<n;v++){ int d=0; for(int i=0;i<deg0[v];i++) if((R>>adjc[v][i])&1) d++; if(d&1) odd++; }
  if(odd>2*t) return 0;
  int e=__builtin_ctzll(R);
  int u=eu[e], v=ev[e];
  return armL(R,t,1ULL<<e,(1<<u)|(1<<v),u,v);
}

int main(int argc, char**argv){
  if(argc<5){ fprintf(stderr,"usage\n"); return 1; }
  n=atoi(argv[1]); k=atoi(argv[2]); q=atoi(argv[3]); mode=atoi(argv[4]); xpos = argc>5?atoi(argv[5]):0;
  ne=0; for(int a=0;a<n;a++) for(int b=a+1;b<n;b++){ eid[a][b]=eid[b][a]=ne; eu[ne]=a; ev[ne]=b; ne++; }
  for(int a=0;a<n;a++){ deg0[a]=0; for(int b=0;b<n;b++) if(b!=a){ adjl[a][deg0[a]]=b; adjc[a][deg0[a]]=eid[a][b]; deg0[a]++; } }
  Pmask=0; for(int i=0;i+1<k;i++) Pmask|=1ULL<<eid[i][i+1];
  for(int L=3; L<=n; L++) for(int s=0;s<n;s++){ memset(used,0,sizeof used); cv[0]=s; used[s]=1;
      /* need all other vertices > s */
      gen(1,L); }
  fprintf(stderr,"n=%d k=%d q=%d mode=%d xpos=%d cycles=%d\n",n,k,q,mode,xpos,ncyc);
  long long tested=0, fails=0;
  int idx[8];
  /* iterative enumeration of q-subsets with pairwise disjointness */
  u64 acc[9]; acc[0]=Pmask;
  int d=0; idx[0]=-1;
  while(d>=0){
    idx[d]++;
    if(idx[d]>=ncyc){ d--; continue; }
    if(cyc[idx[d]] & acc[d]) continue;
    acc[d+1]=acc[d]|cyc[idx[d]];
    if(d+1==q){
      tested++;
      u64 R=acc[q];
      if(!search(R,q+1)){
        fails++;
        printf("FAIL:");
        for(int i=0;i<q;i++){ int c=idx[i]; int L=cycv[c*(n+1)]; printf(" ("); for(int j=0;j<L;j++) printf("%d%s",cycv[c*(n+1)+1+j],j+1<L?",":""); printf(")"); }
        printf("\n"); fflush(stdout);
      }
    } else { idx[d+1]=idx[d]; d++; }
  }
  fprintf(stderr,"tested=%lld fails=%lld nodes=%lld\n",tested,fails,nodes);
  printf("SUMMARY n=%d k=%d q=%d mode=%d xpos=%d cycles=%d tested=%lld fails=%lld\n",n,k,q,mode,xpos,ncyc,tested,fails);
  return 0;
}
