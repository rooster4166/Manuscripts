/* Random test of the short-path-and-cycles statement on larger vertex pools.
 *
 * Usage: rflower N k q mode trials seed maxlen [star]
 *   pool of N vertices (N <= 30), P = (0,...,k-1)
 *   mode 0: each cycle meets V(P); mode 1: each cycle contains x = xpos
 *   (xpos is given by the environment variable XPOS, default 0)
 *   cycles are random sequences of distinct pool vertices of length 3..maxlen,
 *   biased to reuse P-vertices and previously used vertices (to create overlaps);
 *   a candidate is rejected if it reuses an edge.
 *   With star=1 additionally tests property (*) for the first q-1 cycles:
 *   P u C_1 u ... u C_{q-1} has a partition into q paths one of which contains x
 *   and has at most 6 vertices.
 * Prints failures and counts.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int N,k,q,mode,xpos;
static int eid[32][32], eu[512], ev[512], ne;
static int adjl[32][32], adjc[32][32], deg0[32];
static int nverts;
/* edges up to 128 used: we map only edges actually present to compact ids */
static int cid[32][32]; static int cu[128], cv_[128]; static int nce;
static int cadj[32][32], cadje[32][32], cdeg[32];
static u128 ONE=1;
static int search(u128 R,int t);
static int armR(u128 R,int t,u128 pe,unsigned vis,int end){
  for(int i=0;i<cdeg[end];i++){int w=cadj[end][i],e=cadje[end][i];
    if(!((R>>e)&1)||((pe>>e)&1)||((vis>>w)&1)) continue;
    if(armR(R,t,pe|(ONE<<e),vis|(1u<<w),w)) return 1;}
  if(search(R&~pe,t-1)) return 1;
  return 0;}
static int armL(u128 R,int t,u128 pe,unsigned vis,int end,int v){
  for(int i=0;i<cdeg[end];i++){int w=cadj[end][i],e=cadje[end][i];
    if(!((R>>e)&1)||((pe>>e)&1)||((vis>>w)&1)) continue;
    if(armL(R,t,pe|(ONE<<e),vis|(1u<<w),w,v)) return 1;}
  if(armR(R,t,pe,vis,v)) return 1;
  return 0;}
static int popc(u128 R){return __builtin_popcountll((uint64_t)R)+__builtin_popcountll((uint64_t)(R>>64));}
static int ctz(u128 R){uint64_t lo=(uint64_t)R; if(lo) return __builtin_ctzll(lo); return 64+__builtin_ctzll((uint64_t)(R>>64));}
static int search(u128 R,int t){
  if(!R) return 1; if(t==0) return 0;
  /* vertices present */
  int nv=0, odd=0;
  for(int v=0;v<N;v++){int d=0; for(int i=0;i<cdeg[v];i++) if((R>>cadje[v][i])&1) d++; if(d){nv++; if(d&1) odd++;}}
  if(popc(R)>t*(nv-1)) return 0; if(odd>2*t) return 0;
  int e=ctz(R); int u=cu[e],v=cv_[e];
  return armL(R,t,ONE<<e,(1u<<u)|(1u<<v),u,v);
}
/* property (*): some path through x with <=6 vertices, remainder into t-1 paths */
static int starR(u128 R,int t,u128 pe,unsigned vis,int end,int nvq){
  if(((vis>>xpos)&1) && search(R&~pe,t-1)) return 1;
  if(nvq>=6) return 0;
  for(int i=0;i<cdeg[end];i++){int w=cadj[end][i],e=cadje[end][i];
    if(!((R>>e)&1)||((pe>>e)&1)||((vis>>w)&1)) continue;
    if(starR(R,t,pe|(ONE<<e),vis|(1u<<w),w,nvq+1)) return 1;}
  return 0;}
static int star(u128 R,int t){
  /* enumerate paths starting at each vertex s (both orientations, fine) */
  for(int s=0;s<N;s++) if(starR(R,t,0,1u<<s,s,1)) return 1;
  return 0;}
static unsigned long long rs;
static unsigned rnd(){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (unsigned)(rs>>11);}
int main(int argc,char**argv){
  N=atoi(argv[1]);k=atoi(argv[2]);q=atoi(argv[3]);mode=atoi(argv[4]);
  long trials=atol(argv[5]); rs=strtoull(argv[6],0,10)*2654435761ULL+1; int maxlen=atoi(argv[7]);
  int dostar = argc>8?atoi(argv[8]):0;
  xpos = getenv("XPOS")?atoi(getenv("XPOS")):0;
  long tested=0,fails=0,starfails=0;
  for(long tr=0;tr<trials;tr++){
    static int used[32][32]; memset(used,0,sizeof used);
    for(int i=0;i+1<k;i++){used[i][i+1]=used[i+1][i]=1;}
    int cyc[8][32], clen[8]; int ok=1;
    int poolw[32]; for(int v=0;v<N;v++) poolw[v]=1; for(int v=0;v<k;v++) poolw[v]=4;
    for(int c=0;c<q && ok;c++){
      int got=0;
      for(int att=0;att<200 && !got;att++){
        int L=3+rnd()%(maxlen-2); if(L>N) L=N;
        int seq[32], in[32]; memset(in,0,sizeof in);
        int s;
        if(mode==1) s=xpos; else s=rnd()%k;
        seq[0]=s; in[s]=1; int bad=0;
        for(int i=1;i<L;i++){
          /* weighted choice among unused vertices avoiding used edges */
          int tot=0; for(int v=0;v<N;v++) if(!in[v] && !used[seq[i-1]][v]) tot+=poolw[v];
          if(!tot){bad=1;break;}
          int r=rnd()%tot, v; for(v=0;v<N;v++){ if(in[v]||used[seq[i-1]][v]) continue; r-=poolw[v]; if(r<0) break;}
          seq[i]=v; in[v]=1;
        }
        if(bad) continue;
        if(used[seq[L-1]][seq[0]]) continue;
        /* accept */
        for(int i=0;i<L;i++){int a=seq[i],b=seq[(i+1)%L]; used[a][b]=used[b][a]=1;}
        for(int i=0;i<L;i++){cyc[c][i]=seq[i]; poolw[seq[i]]+=2;}
        clen[c]=L; got=1;
      }
      if(!got) ok=0;
    }
    if(!ok) continue;
    /* build compact edge ids */
    nce=0; memset(cdeg,0,sizeof cdeg);
    for(int a=0;a<N;a++) for(int b=a+1;b<N;b++) if(used[a][b]){
      if(nce>=128){ok=0;break;} cid[a][b]=cid[b][a]=nce; cu[nce]=a; cv_[nce]=b;
      cadj[a][cdeg[a]]=b; cadje[a][cdeg[a]]=nce; cdeg[a]++;
      cadj[b][cdeg[b]]=a; cadje[b][cdeg[b]]=nce; cdeg[b]++; nce++; }
    if(!ok) continue;
    u128 R=0; for(int e=0;e<nce;e++) R|=ONE<<e;
    tested++;
    if(!search(R,q+1)){
      fails++; printf("FAIL k=%d:",k);
      for(int c=0;c<q;c++){printf(" (");for(int i=0;i<clen[c];i++) printf("%d%s",cyc[c][i],i+1<clen[c]?",":""); printf(")");}
      printf("\n"); fflush(stdout);
    }
    if(dostar){
      /* P plus first q-1 cycles */
      u128 R2=0; for(int i=0;i+1<k;i++) R2|=ONE<<cid[i][i+1];
      for(int c=0;c<q-1;c++) for(int i=0;i<clen[c];i++){int a=cyc[c][i],b=cyc[c][(i+1)%clen[c]]; R2|=ONE<<cid[a][b];}
      if(!star(R2,q)){
        starfails++; printf("STARFAIL k=%d:",k);
        for(int c=0;c<q-1;c++){printf(" (");for(int i=0;i<clen[c];i++) printf("%d%s",cyc[c][i],i+1<clen[c]?",":""); printf(")");}
        printf("\n"); fflush(stdout);
      }
    }
  }
  printf("SUMMARY N=%d k=%d q=%d mode=%d xpos=%d maxlen=%d tested=%ld fails=%ld starfails=%ld\n",N,k,q,mode,xpos,maxlen,tested,fails,starfails);
  return 0;
}
