/* A42 jcov.c -- own implementation of the proved conditions on L_N(2) instances (no project code).
   Input: lines 'g6 c1 a1 c2 a2'.  For each instance:
     joined?  If joined, every joint path P (c1 -> c2 avoiding a1, a2), K0 = F - E(P):
       C1 leaf: d_F(c1) = 1 or d_F(c2) = 1                       (Prop 6.1)
       C2 suppression: an end with exactly 2 neighbours in K0, non-adjacent in K0 (Prop 6.2)
       C3 trail: a steering trail from g avoiding N_K0[h], {g,h} = {c1,c2} (Thm 6.3), exhaustive DFS
       C3 tjoin: Lemma 6.4's criterion (own implementation), compared with C3 trail
     B (Cor. B of ln) and G (Thm 7.1, either orientation) for separated instances.
   Output: per-instance line 'g6 c1 a1 c2 a2 | J/S npaths C1 C2 C3 B G' on stdout; summary on stderr;
   if argv[1] given, writes every joint path's K0 as 'K0g6 c1 c2 class P' to it (class: act=both ends of
   positive degree in K0, 2c = 2-connected on non-isolated vertices, O1 = odd vertex of degree n_act-1). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n; static uint32_t F[16], K[16];
static int dec(const char*s){ n=s[0]-63; int bit=0,cur=0; const char*p=s+1; memset(F,0,sizeof F);
  for(int j=1;j<n;j++)for(int i=0;i<j;i++){ if(!bit){cur=*p++-63;bit=6;} bit--; if(cur>>bit&1){F[i]|=1u<<j;F[j]|=1u<<i;} } return 1;}
static void enc(uint32_t*A,char*out){ int p=0; out[p++]=63+n; int acc=0,b=0;
  for(int j=1;j<n;j++)for(int i=0;i<j;i++){ acc=acc<<1|(A[i]>>j&1); if(++b==6){out[p++]=63+acc;acc=0;b=0;} }
  if(b){acc<<=6-b; out[p++]=63+acc;} out[p]=0; }
static int pc(uint32_t x){return __builtin_popcount(x);}
static uint32_t comp(const uint32_t*A,int s,uint32_t allowed){ uint32_t seen=1u<<s,fr=seen; while(fr){int x=__builtin_ctz(fr);fr&=fr-1; uint32_t nb=A[x]&allowed&~seen; seen|=nb; fr|=nb;} return seen;}
/* ---- trail search ---- */
#define TH (1<<20)
static uint64_t tkey[TH]; static unsigned char tused[TH]; static int tcnt; static int eidx[16][16]; static int ne;
static uint64_t kmask(const uint32_t*A){ uint64_t m=0; for(int u=0;u<n;u++){uint32_t x=A[u]&~((2u<<u)-1); while(x){int v=__builtin_ctz(x);x&=x-1; m|=1ULL<<eidx[u][v];}} return m;}
static int memo(uint64_t k){ uint64_t h=(k*0x9E3779B97F4A7C15ULL)>>44; for(;;){ h&=TH-1; if(!tused[h]){tused[h]=1;tkey[h]=k;tcnt++;return 0;} if(tkey[h]==k) return 1; h++; } }
static uint32_t TA[16];
static int trail(int p, uint32_t X){
  uint64_t k=(kmask(TA)<<4)|(uint64_t)p; if(tcnt>TH/2) {fprintf(stderr,"memo full\n"); exit(1);} if(memo(k)) return 0;
  uint32_t c=TA[p]&~X;
  while(c){ int u=__builtin_ctz(c); c&=c-1;
    if(pc(TA[u])==1) return 1;                    /* u isolated after the move: retire */
    TA[p]&=~(1u<<u); TA[u]&=~(1u<<p);
    int r=trail(u,X);
    TA[p]|=1u<<u; TA[u]|=1u<<p;
    if(r) return 1; }
  return 0; }
static int steer(int g,int h){ memcpy(TA,K,sizeof TA); memset(tused,0,sizeof tused); tcnt=0;
  uint32_t X=K[h]|1u<<h; return trail(g,X); }
/* ---- Lemma 6.4 criterion ---- g not in X; A is the current graph */
static int crit(const uint32_t*A,int g,uint32_t X){
  uint32_t VH=((1u<<n)-1)&~X; VH|=1u<<g;
  for(int t=0;t<n;t++){ if(!(VH>>t&1)||!A[t]) continue;
    if(A[t]&~VH) continue;                         /* N(t) subset of V(H) */
    uint32_t T = (t!=g)? (A[t]^(1u<<g)) : A[g];
    uint32_t rest=VH&~(1u<<t), seen=0; int ok=1;
    for(int s=0;s<n&&ok;s++){ if(!(rest>>s&1)||(seen>>s&1)) continue; uint32_t c=comp(A,s,rest); seen|=c; if(pc(c&T)%2) ok=0; }
    if(ok) return 1; }
  return 0; }
static int tjoin(int g,int h){ uint32_t X=K[h]|1u<<h;
  if(!(X>>g&1)) return crit(K,g,X);
  uint32_t c=K[g]&~X;
  while(c){ int u=__builtin_ctz(c); c&=c-1; if(pc(K[u])==1) return 1;
    uint32_t A2[16]; memcpy(A2,K,sizeof A2); A2[g]&=~(1u<<u); A2[u]&=~(1u<<g); if(crit(A2,u,X)) return 1; }
  return 0; }
/* ---- B and G ---- */
static int corB(int c1,int a1,int c2,int a2){
  for(int x=0;x<n;x++) if((F[x]>>a1&1)&&(F[x]>>a2&1)) return 0;
  int c[2]={c1,c2},a[2]={a1,a2};
  for(int t=0;t<2;t++) if(pc(F[c[t]])==1){int w=__builtin_ctz(F[c[t]]); if(a[t]!=w&&!(F[w]>>a[t]&1)) return 1;}
  return 0;}
static int glue(int ci,int ai,int cj,int aj){ int v=aj; uint32_t all=(1u<<n)-1; uint32_t B=comp(F,cj,all&~(1u<<v));
  if(B>>ci&1) return 0; if(!(B>>ai&1)) return 1; if(pc(F[v]&B)%2) return 1; if(!(F[v]>>ci&1)) return 1;
  uint32_t C=comp(F,ci,all&~(1u<<v)); return (C&~F[v])!=0; }
static int twoconn(void){ uint32_t act=0; for(int v=0;v<n;v++) if(K[v]) act|=1u<<v; if(!act) return 0;
  int s=__builtin_ctz(act); if(comp(K,s,act)!=act) return 0;
  for(int x=0;x<n;x++) if(act>>x&1){ uint32_t r=act&~(1u<<x); if(!r) continue; int s2=__builtin_ctz(r); if(comp(K,s2,r)!=r) return 0; }
  return 1; }
/* ---- joint paths ---- */
static int path[16], plen; static FILE*fk; static char g6s[64];
static int c1,a1,c2,a2, np, f1,f2,f3, agree, disagree, dTF, dFT; static long tot_paths, cls[2][2][2][2];
static void onpath(void){
  memcpy(K,F,sizeof K); for(int i=0;i+1<plen;i++){ K[path[i]]&=~(1u<<path[i+1]); K[path[i+1]]&=~(1u<<path[i]); }
  np++; tot_paths++;
  int s2=0; for(int t=0;t<2;t++){ int c=t?c2:c1; if(pc(K[c])==2){ int y=__builtin_ctz(K[c]); int z=31-__builtin_clz(K[c]); if(!(K[y]>>z&1)) s2=1; } }
  if(s2) f2=1;
  int act = K[c1] && K[c2];
  for(int t=0;t<2;t++){ int g=t?c2:c1, h=t?c1:c2; int a=steer(g,h), b=tjoin(g,h);
    if(a) f3=1;
    if(act){ if(a==b) agree++; else { disagree++; if(a) dTF++; else dFT++; } } }
  if(fk){ int na=0; for(int v=0;v<n;v++) if(K[v]) na++; int o1=0; for(int v=0;v<n;v++) if(K[v] && pc(K[v])%2==1 && pc(K[v])==na-1) o1=1;
    int tc=twoconn(); char o[64]; enc(K,o); fprintf(fk,"%s %d %d %s %s %s |",o,c1,c2,act?"act":"iso",tc?"2c":"n2c",o1?"O1":"-");
    for(int i=0;i<plen;i++) fprintf(fk,i?"-%d":" %d",path[i]); fprintf(fk,"\n"); }
}
static void dfs(uint32_t used){ int x=path[plen-1]; if(x==c2){ onpath(); return; }
  uint32_t c=F[x]&~used&~(1u<<a1)&~(1u<<a2); while(c){int y=__builtin_ctz(c);c&=c-1; path[plen++]=y; dfs(used|1u<<y); plen--; } }
int main(int argc,char**argv){
  fk = argc>1 ? fopen(argv[1],"w") : NULL;
  char line[256]; long ninst=0,nj=0,nC1=0,nC2=0,nC3=0,nU=0,nB=0,nG=0,nAll=0;
  while(fgets(line,sizeof line,stdin)){ if(sscanf(line,"%63s %d %d %d %d",g6s,&c1,&a1,&c2,&a2)!=5) continue; dec(g6s);
    ne=0; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++) eidx[u][v]=eidx[v][u]=ne++;
    ninst++; uint32_t all=(1u<<n)-1; int joined = comp(F,c1,all&~(1u<<a1)&~(1u<<a2))>>c2&1;
    np=0; f1=0;f2=0;f3=0; int b=corB(c1,a1,c2,a2), g=0;
    if(joined){ nj++; f1 = pc(F[c1])==1 || pc(F[c2])==1; path[0]=c1; plen=1; dfs(1u<<c1); nC1+=f1; nC2+=f2; nC3+=f3; nU+= (f1||f2||f3); }
    else g = glue(c1,a1,c2,a2)||glue(c2,a2,c1,a1);
    nB+=b; nG+=g; nAll += (b||g||f1||f2||f3);
    printf("%s %d %d %d %d | %c %d %d %d %d %d %d\n",g6s,c1,a1,c2,a2,joined?'J':'S',np,f1,f2,f3,b,g);
  }
  fprintf(stderr,"instances %ld joined %ld joint-paths %ld | on joined: C1 %ld C2 %ld C3 %ld union %ld | B %ld G %ld | covered (B,C1,C2,C3,G) %ld residual %ld\n",
    ninst,nj,tot_paths,nC1,nC2,nC3,nU,nB,nG,nAll,ninst-nAll);
  fprintf(stderr,"Lemma 6.4 vs trail search (joint paths with both ends active, both orientations): agree %d disagree %d (trail yes/tjoin no %d, trail no/tjoin yes %d)\n",agree,disagree,dTF,dFT);
  if(fk) fclose(fk); return 0; }
