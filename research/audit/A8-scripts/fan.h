/* Shared Fan-restoration certificate machinery on up to 8 local sites.
   Semantics (MR Thm 124 / p.131 / Lemma 133):
   state = (M = still-missing local edges, b = lower bounds on end counts).
   A node chooses receiver w and nonempty donor set S subset {t: wt in M, b(t)>0} with
       sum_{t in S} b(t) > #{x : wx in E(G)\M, b(x)=0}
   and must win for EVERY child (restore wt, b(w)++, b(t)--), t in S.
   Leaf: M empty and leafcond(b) holds. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t u32;
static int NV=7;
static int EIDX[8][8];
static int EU[28], EV[28];
static int NE=21;
static void init_edges(int n){ NV=n; int k=0; for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){EIDX[i][j]=EIDX[j][i]=k;EU[k]=i;EV[k]=j;k++;} NE=k; }
static u32 INC[8]; /* incident edge masks */
static void init_inc(void){ for(int v=0;v<NV;v++){INC[v]=0;} for(int e=0;e<NE;e++){INC[EU[e]]|=1u<<e; INC[EV[e]]|=1u<<e;} }
static int popc(u32 x){ return __builtin_popcount(x); }
/* leaf condition: mode 0 none; mode 1: b[LEAFV] >= LEAFMIN */
static int LEAFMODE=0, LEAFV=0, LEAFMIN=0;
static long NODES=0;
static int win(u32 G, u32 M, int *b){
  NODES++;
  if(!M){ if(LEAFMODE==1) return b[LEAFV]>=LEAFMIN; return 1; }
  u32 cur = G & ~M;
  for(int w=0;w<NV;w++){
    u32 mw = M & INC[w]; if(!mw) continue;
    int cand[8], nc=0;
    for(u32 m=mw;m;m&=m-1){ int e=__builtin_ctz(m); int t = EU[e]==w?EV[e]:EU[e]; if(b[t]>0) cand[nc++]=t; }
    if(!nc) continue;
    int z=0; for(u32 m=cur&INC[w];m;m&=m-1){ int e=__builtin_ctz(m); int x = EU[e]==w?EV[e]:EU[e]; if(b[x]==0) z++; }
    for(int S=1;S<(1<<nc);S++){
      int sum=0; for(int i=0;i<nc;i++) if(S>>i&1) sum+=b[cand[i]];
      if(sum<=z) continue;
      /* minimality pruning: skip S if some proper subset already satisfies (dominated) */
      int dominated=0;
      for(int i=0;i<nc && !dominated;i++) if(S>>i&1){ if(sum-b[cand[i]]>z) dominated=1; }
      if(dominated) continue;
      int ok=1;
      for(int i=0;i<nc && ok;i++) if(S>>i&1){ int t=cand[i]; int e=EIDX[w][t];
        b[w]++; b[t]--; ok = win(G, M & ~(1u<<e), b); b[w]--; b[t]++; }
      if(ok) return 1;
    }
  }
  return 0;
}
/* union-find forest check on vertex set Zmask within edge set E */
static int is_forest(u32 E, int Zmask){
  int par[8]; for(int i=0;i<NV;i++) par[i]=i;
  for(u32 m=E;m;m&=m-1){ int e=__builtin_ctz(m); int u=EU[e], v=EV[e];
    if(!((Zmask>>u)&1) || !((Zmask>>v)&1)) continue;
    while(par[u]!=u) u=par[u]; while(par[v]!=v) v=par[v];
    if(u==v) return 0; par[u]=v; }
  return 1;
}
