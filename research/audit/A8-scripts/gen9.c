/* Generate all 2-connected graphs on 9 vertices up to isomorphism by extending connected 8-vertex graphs.
   Canonical form: equitable colour refinement + exhaustive within-cell permutations (lexicographic max code). */
#include "pn.h"
#define N 9
static int A[N][N];
static int col[N];
static void refine(void){
  for(int v=0;v<N;v++){ int d=0; for(int u=0;u<N;u++) d+=A[v][u]; col[v]=d; }
  for(int it=0;it<N;it++){
    long sig[N][N+1];
    for(int v=0;v<N;v++){ int c[N],k=0; for(int u=0;u<N;u++) if(A[v][u]) c[k++]=col[u];
      for(int i=0;i<k;i++) for(int j=i+1;j<k;j++) if(c[j]<c[i]){int t=c[i];c[i]=c[j];c[j]=t;}
      sig[v][0]=col[v]; for(int i=0;i<N;i++) sig[v][i+1]= i<k? c[i] : -1; }
    /* rank signatures */
    int nc[N]; int changed=0;
    for(int v=0;v<N;v++){ int r=0; for(int u=0;u<N;u++){ int cmp=0; for(int i=0;i<=N;i++){ if(sig[u][i]!=sig[v][i]){ cmp = sig[u][i]<sig[v][i]?-1:1; break;} } if(cmp<0){ /* count distinct smaller sigs */ int dup=0; for(int w=0;w<u;w++){ int same=1; for(int i=0;i<=N;i++) if(sig[w][i]!=sig[u][i]){same=0;break;} if(same){dup=1;break;} } if(!dup) r++; } } nc[v]=r; }
    for(int v=0;v<N;v++) if(nc[v]!=col[v]) changed=1;
    int distinct_old=0,distinct_new=0; for(int v=0;v<N;v++){ int f=1; for(int u=0;u<v;u++) if(col[u]==col[v]) f=0; distinct_old+=f; f=1; for(int u=0;u<v;u++) if(nc[u]==nc[v]) f=0; distinct_new+=f; }
    for(int v=0;v<N;v++) col[v]=nc[v];
    if(distinct_new==distinct_old && it>0) break;
    (void)changed;
  }
}
static int order[N]; static int perm[N]; static int used[N]; static u64 best; static int haveb;
static int cellstart[N+1], ncell;
static void search(int pos, u64 code, int bitpos){
  if(pos==N){ if(!haveb || code>best){best=code;haveb=1;} return; }
  /* position pos must be filled by a vertex of the colour class for this position */
  int c = order[pos];
  for(int v=0;v<N;v++) if(!used[v] && col[v]==c){
    /* bits for pairs (i,pos) i<pos */
    u64 nc=code; int bp=bitpos;
    for(int i=0;i<pos;i++){ nc = (nc<<1) | (u64)A[perm[i]][v]; bp++; }
    /* prune: compare prefix with best's prefix */
    if(haveb){ u64 bpre = best >> (36-bp); if(nc < bpre) continue; }
    used[v]=1; perm[pos]=v; search(pos+1,nc,bp); used[v]=0;
  }
}
static u64 canon(void){
  refine();
  /* positions ordered by colour ascending */
  int k=0; for(int c=0;c<N;c++) for(int v=0;v<N;v++) if(col[v]==c) order[k++]=c;
  haveb=0; memset(used,0,sizeof used); search(0,0,0); return best;
}
static int biconn(void){
  for(int x=-1;x<N;x++){ int seen=0, st[N], sp=0; int s = (x==0)?1:0; seen|=1<<s; st[sp++]=s;
    while(sp){ int v=st[--sp]; for(int u=0;u<N;u++) if(A[v][u] && u!=x && !(seen>>u&1)){ seen|=1<<u; st[sp++]=u; } }
    int need = ((1<<N)-1) & ~(x>=0?1<<x:0); if(seen!=need) return 0; }
  return 1;
}
/* hash set of codes */
#define SB 24
static u64 *set; static long nset;
static int insert(u64 c){ u64 h=((c+1)*0x9E3779B97F4A7C15ULL)>>(64-SB); while(set[h]){ if(set[h]==c+1) return 0; h=(h+1)&((1ULL<<SB)-1);} set[h]=c+1; nset++; return 1; }
int main(){
  set=calloc(1ULL<<SB,8); char line[256]; int adj[16][16]; long tried=0;
  while(fgets(line,sizeof line,stdin)){ line[strcspn(line,"\n")]=0; int n=g6decode(line,adj); if(n!=8) continue;
    for(int S=1;S<256;S++){ memset(A,0,sizeof A); for(int i=0;i<8;i++) for(int j=0;j<8;j++) A[i][j]=adj[i][j];
      for(int i=0;i<8;i++) if(S>>i&1) A[8][i]=A[i][8]=1;
      if(!biconn()) continue; tried++;
      u64 c=canon();
      if(insert(c)){ /* output graph6 of canonical? output this labelled graph */
        char out[32]; out[0]=63+N; int k=0,val=0,bits=0,p=1;
        for(int j=1;j<N;j++) for(int i=0;i<j;i++){ val=(val<<1)|A[i][j]; bits++; if(bits==6){ out[p++]=63+val; val=0; bits=0; } }
        if(bits){ val<<=(6-bits); out[p++]=63+val; } out[p]=0; puts(out); (void)k; }
    } }
  fprintf(stderr,"tried %ld biconnected labelled, distinct %ld\n",tried,nset);
}
