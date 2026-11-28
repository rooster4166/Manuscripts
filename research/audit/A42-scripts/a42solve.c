/* a42solve.c -- A42 audit: independent exact solver for constrained parity path decompositions.
   Own code; shares nothing with lnsolve.c / lnsolve3.c.  Same query language:
     <graph6> [A t a] [S p q] [J p q] [R v k]   (A: every path with an end at t misses a;
     S: no path contains both p and q; J: p, q are the two ends of one path (needs r(p)=r(q)=1);
     R: r(v) = k required ends, default d(v) mod 2).
   Method: exact cover by paths, branching on ONE uncovered edge e = xy (at a vertex of least
   remaining degree): every simple path through e, with both ends at vertices with unspent ends,
   is tried.  Pruning: r(v) <= remaining degree; every component of remaining edges has >= 2
   unspent ends; failure memo on (remaining edges, unspent ends).  No degree bound.
   Output: SAT <g6> :: p-q-r ; ... | UNSAT <g6> | UNDEC <g6> (node budget -b). n <= 11. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MX 12
static int n, m, E_u[80], E_v[80], eid[MX][MX];
static int rem[MX], rdeg[MX]; static uint64_t rmask; /* remaining edges */
static uint32_t avoidOf[MX], sepOf[MX]; static int mateOf[MX];
static long long nodes, budget; static int aborted;
static int sol[400][MX+1], sollen[400], nsol;
/* memo */
#define HB 22
#define HS (1u<<HB)
static uint64_t *hk1, *hk2; static unsigned char *hu; static long hc;
static uint64_t remcode(void){ uint64_t c=0; for(int v=0;v<n;v++) c=c*3+rem[v]; return c; }
static uint64_t mixh(uint64_t x){ x^=x>>31; x*=0x9E3779B97F4A7C15ULL; x^=x>>29; x*=0xBF58476D1CE4E5B9ULL; x^=x>>32; return x; }
static int mhas(uint64_t a,uint64_t b){ uint64_t h=mixh(a*31+mixh(b))&(HS-1); for(int i=0;i<128;i++){uint64_t j=(h+i)&(HS-1); if(!hu[j])return 0; if(hk1[j]==a&&hk2[j]==b)return 1;} return 0; }
static void madd(uint64_t a,uint64_t b){ if(hc>(long)(HS*0.6))return; uint64_t h=mixh(a*31+mixh(b))&(HS-1); for(int i=0;i<128;i++){uint64_t j=(h+i)&(HS-1); if(!hu[j]){hu[j]=1;hk1[j]=a;hk2[j]=b;hc++;return;}} }
static uint32_t nbr(int v){ uint32_t r=0; for(int w=0;w<n;w++) if(w!=v && eid[v][w]>=0 && (rmask>>eid[v][w]&1)) r|=1u<<w; return r; }
static int ok_state(void){
  for(int v=0;v<n;v++) if(rem[v]>rdeg[v]) return 0;
  uint32_t seen=0;
  for(int v=0;v<n;v++){ if(!rdeg[v]||(seen>>v&1)) continue;
    uint32_t c=1u<<v, fr=c; while(fr){int x=__builtin_ctz(fr); fr&=fr-1; uint32_t nb=nbr(x)&~c; c|=nb; fr|=nb;}
    seen|=c; int e=0; for(int x=0;x<n;x++) if(c>>x&1) e+=rem[x]; if(e<2) return 0; }
  return 1;
}
static int search(void);
static int LS[200][MX+1], RS[200][MX+1]; static int depth; static int *L, *R;
/* is the path (L reversed) + (R) acceptable w.r.t. constraints: ends u=L[ll-1], w=R[rl-1] */
static int path_ok(int ll,int rl){
  int u=L[ll-1], w=R[rl-1]; uint32_t vs=0;
  for(int i=0;i<ll;i++) vs|=1u<<L[i];
  for(int i=0;i<rl;i++) vs|=1u<<R[i];
  if(!rem[u]||!rem[w]) return 0;
  if(avoidOf[u]&vs) return 0;
  if(avoidOf[w]&vs) return 0;
  for(int x=0;x<n;x++) if((vs>>x&1)&&(sepOf[x]&vs)) return 0;
  if(mateOf[u]>=0 && mateOf[u]!=w) return 0;
  if(mateOf[w]>=0 && mateOf[w]!=u) return 0;
  return 1;
}
static int try_path(int ll,int rl){
  if(!path_ok(ll,rl)) return 0;
  /* apply: edges L[i]L[i+1], L[0]R[0], R[i]R[i+1] */
  uint64_t old=rmask; int pv[2*MX+2], np=0;
  for(int i=ll-1;i>=0;i--) pv[np++]=L[i]; for(int i=0;i<rl;i++) pv[np++]=R[i];
  for(int i=0;i+1<np;i++){ rmask&=~(1ULL<<eid[pv[i]][pv[i+1]]); rdeg[pv[i]]--; rdeg[pv[i+1]]--; }
  rem[pv[0]]--; rem[pv[np-1]]--;
  memcpy(sol[nsol],pv,sizeof(int)*np); sollen[nsol]=np; nsol++;
  int r = 0;
  if(ok_state()){ depth++; r = search(); depth--; L=LS[depth]; R=RS[depth]; }
  if(r) return 1;
  nsol--; rem[pv[0]]++; rem[pv[np-1]]++;
  for(int i=0;i+1<np;i++){ rdeg[pv[i]]++; rdeg[pv[i+1]]++; } rmask=old;
  return 0;
}
static int extR(int ll,int rl,uint32_t used){
  if(aborted) return 0;
  if(try_path(ll,rl)) return 1;
  if(aborted) return 0;
  int y=R[rl-1]; uint32_t c=nbr(y)&~used;
  while(c){ int z=__builtin_ctz(c); c&=c-1;
    /* the edge y z is used by the path: temporarily mark */
    R[rl]=z; if(extR(ll,rl+1,used|1u<<z)) return 1; if(aborted) return 0; }
  return 0;
}
/* careful: nbr() reads rmask, which still contains the path's edges during enumeration; since the
   path is simple (vertex-disjoint by 'used'), no edge is used twice. */
static int extL(int ll,uint32_t used,int y){
  if(aborted) return 0;
  R[0]=y; if(extR(ll,1,used|1u<<y)) return 1; if(aborted) return 0;
  int x=L[ll-1]; uint32_t c=nbr(x)&~used&~(1u<<y);
  while(c){ int z=__builtin_ctz(c); c&=c-1; L[ll]=z; if(extL(ll+1,used|1u<<z,y)) return 1; if(aborted) return 0; }
  return 0;
}
static int search(void){
  if(++nodes>budget){aborted=1;return 0;}
  if(!rmask){ for(int v=0;v<n;v++) if(rem[v]) return 0; return 1; }
  uint64_t k2=remcode(); if(mhas(rmask,k2)) return 0;
  /* branch edge: at the vertex of least positive remaining degree, its lowest neighbour */
  int bx=-1,bd=99; for(int v=0;v<n;v++) if(rdeg[v]>0 && rdeg[v]<bd){bd=rdeg[v];bx=v;}
  int by=__builtin_ctz(nbr(bx));
  L=LS[depth]; R=RS[depth];
  L[0]=bx; int r=extL(1,1u<<bx,by);
  if(!r && !aborted) madd(rmask,k2);
  return r;
}
static int dec(const char*s){ n=s[0]-63; if(n<1||n>MX-1) return 0; int bit=0,cur=0; const char*p=s+1; m=0;
  for(int i=0;i<MX;i++)for(int j=0;j<MX;j++) eid[i][j]=-1;
  for(int j=1;j<n;j++)for(int i=0;i<j;i++){ if(!bit){cur=*p++-63;bit=6;} bit--; if(cur>>bit&1){E_u[m]=i;E_v[m]=j;eid[i][j]=eid[j][i]=m;m++;} }
  return 1; }
int main(int argc,char**argv){
  budget=200000000LL; for(int i=1;i<argc;i++) if(!strcmp(argv[i],"-b")&&i+1<argc) budget=atoll(argv[++i]);
  hk1=malloc(8*HS); hk2=malloc(8*HS); hu=malloc(HS);
  static char line[1<<16]; setvbuf(stdout,NULL,_IOLBF,0);
  while(fgets(line,sizeof line,stdin)){
    char*t=strtok(line," \t\n"); if(!t) continue; char g6[128]; strncpy(g6,t,127); g6[127]=0;
    if(!dec(g6)){printf("BAD %s\n",g6);continue;}
    int deg[MX]={0}; for(int e=0;e<m;e++){deg[E_u[e]]++;deg[E_v[e]]++;}
    for(int v=0;v<n;v++){rem[v]=deg[v]%2; avoidOf[v]=0; sepOf[v]=0; mateOf[v]=-1; rdeg[v]=deg[v];}
    int bad=0;
    while((t=strtok(NULL," \t\n"))){ char*xs=strtok(NULL," \t\n"),*ys=strtok(NULL," \t\n"); if(!xs||!ys){bad=1;break;} int x=atoi(xs),y=atoi(ys);
      if(!strcmp(t,"A")) avoidOf[x]|=1u<<y; else if(!strcmp(t,"S")){sepOf[x]|=1u<<y; sepOf[y]|=1u<<x;}
      else if(!strcmp(t,"J")){mateOf[x]=y; mateOf[y]=x;} else if(!strcmp(t,"R")) rem[x]=y; else bad=1; }
    for(int v=0;v<n;v++) if(mateOf[v]>=0 && rem[v]!=1) bad=1;
    if(bad){printf("BAD %s\n",g6);continue;}
    rmask=0; for(int e=0;e<m;e++) rmask|=1ULL<<e;
    nodes=0; aborted=0; nsol=0; depth=0; memset(hu,0,HS); hc=0;
    int par=1, tot=0; for(int v=0;v<n;v++){ if((deg[v]-rem[v])&1) par=0; tot+=rem[v]; }
    int ok = (par && !(tot&1) && ok_state()) ? search() : 0;
    if(ok){ printf("SAT %s ::",g6); for(int i=0;i<nsol;i++){ printf(" "); for(int j=0;j<sollen[i];j++) printf(j?"-%d":"%d",sol[i][j]); if(i+1<nsol) printf(" ;"); } printf("\n"); }
    else if(aborted) printf("UNDEC %s\n",g6); else printf("UNSAT %s\n",g6);
  }
  return 0; }
