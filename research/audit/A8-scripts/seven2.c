/* Independent replay of MR Theorem 124's seven-site finite fact. */
#include "fan.h"
static int DMAX=5; static int ORDER=0;
static unsigned char *memo; /* 0 unknown, 1+ds certified with minimal |D|=ds, 255 fail */
static int certifiable(u32 G){
  if(memo[G]) return memo[G]!=255 ? memo[G] : 0;
  int edges[21], ne=0; for(u32 m=G;m;m&=m-1) edges[ne++]=__builtin_ctz(m);
  for(int ds=0; ds<=DMAX && ds<=ne; ds++){
    /* enumerate combinations of size ds */
    int c[8]; for(int i=0;i<ds;i++) c[i]=i;
    while(1){
      u32 D=0; for(int i=0;i<ds;i++) D|=1u<<edges[c[i]];
      int b[8]; int Z=0;
      for(int v=0;v<NV;v++){ b[v]=popc(D&INC[v])&1; if(!b[v]) Z|=1<<v; }
      if(is_forest(G&~D, Z) && win(G, D, b)){ memo[G]=1+ds; return 1+ds; }
      int i=ds-1; while(i>=0 && c[i]==ne-ds+i) i--; if(i<0) break; c[i]++; for(int j=i+1;j<ds;j++) c[j]=c[j-1]+1;
    }
  }
  memo[G]=255; return 0;
}
/* enumerate simple p-q paths inside vertex set Y of F; store edge masks */
static u32 paths[20000]; static int plen[20000]; static int npaths;
static void dfs(u32 F, int Y, int cur, int q, int vis, u32 em, int len){
  if(cur==q){ paths[npaths]=em; plen[npaths]=len; npaths++; return; }
  for(int v=0;v<NV;v++) if(((Y>>v)&1) && !((vis>>v)&1) && (F>>EIDX[cur][v]&1) && v!=cur){
    dfs(F,Y,v,q,vis|(1<<v),em|(1u<<EIDX[cur][v]),len+1);
  }
}
static int cmpidx_len[20000];
static int cmpfun(const void*a,const void*b){ int x=*(int*)a,y=*(int*)b; return ORDER==0? plen[y]-plen[x] : (ORDER==1? plen[x]-plen[y] : x-y); }
/* admissible A sets for pair p,q with outside sites O (list) */
static int nA; static u32 Aset[64];
static void addA(u32 a){ for(int i=0;i<nA;i++) if(Aset[i]==a) return; Aset[nA++]=a; }
static void gen_lists(u32 F,int p,int q,int *O,int no){
  /* enumerate assignments of each outside site to: none, p-list, q-list, with orders */
  /* brute force: permutations of subsets into two lists */
  nA=0;
  int n=no; /* n<=2 */
  /* represent: list1 sequence, list2 sequence */
  int L1[3],L2[3];
  /* iterate over assignment codes 0..3^n-1 then over orders */
  int pw=1; for(int i=0;i<n;i++) pw*=3;
  for(int code=0;code<pw;code++){
    int a1[3],n1=0,a2[3],n2=0; int c=code;
    for(int i=0;i<n;i++){ int t=c%3; c/=3; if(t==1) a1[n1++]=O[i]; else if(t==2) a2[n2++]=O[i]; }
    /* all orders of a1 and a2 (n1,n2<=2) */
    for(int s1=0;s1<(n1==2?2:1);s1++) for(int s2=0;s2<(n2==2?2:1);s2++){
      int l1[3],l2[3]; int m1=0,m2=0; l1[m1++]=p; l2[m2++]=q;
      for(int i=0;i<n1;i++) l1[m1++]= a1[ s1? n1-1-i : i];
      for(int i=0;i<n2;i++) l2[m2++]= a2[ s2? n2-1-i : i];
      u32 cand=0;
      for(int i=0;i+1<m1;i++){ int e=EIDX[l1[i]][l1[i+1]]; if(F>>e&1) cand|=1u<<e; }
      for(int i=0;i+1<m2;i++){ int e=EIDX[l2[i]][l2[i+1]]; if(F>>e&1) cand|=1u<<e; }
      /* all subsets of cand */
      for(u32 s=cand;;s=(s-1)&cand){ addA(s); if(!s) break; }
    }
  }
  (void)L1;(void)L2;
}
static long nchoices; static long nchoicesA[3];
static unsigned char *Gseen; static long nG; static long dhist[8];
static int check_Y(u32 F, int Y, int record){
  int O[7],no=0; for(int v=0;v<NV;v++) if(!((Y>>v)&1)) O[no++]=v;
  for(int p=0;p<NV;p++) if((Y>>p)&1) for(int q=p+1;q<NV;q++) if((Y>>q)&1){
    gen_lists(F,p,q,O,no);
    npaths=0; dfs(F,Y,p,q,1<<p,0,0);
    int ord[20000]; for(int i=0;i<npaths;i++) ord[i]=i;
    qsort(ord,npaths,sizeof(int),cmpfun);
    for(int ai=0;ai<nA;ai++){
      u32 A=Aset[ai]; int found=0;
      for(int k=0;k<npaths && !found;k++){
        u32 G = F & ~A & ~paths[ord[k]];
        int r=certifiable(G);
        if(r){ found=1; if(record){ if(!Gseen[G]){Gseen[G]=1;nG++;dhist[r-1]++;} } }
      }
      if(!found) return 0;
      if(record){ nchoices++; nchoicesA[popc(A)]++; }
    }
  }
  return 1;
}
int main(int argc,char**argv){
  if(argc>1) DMAX=atoi(argv[1]);
  int skipstruct = argc>2 ? atoi(argv[2]) : 1; if(argc>3) ORDER=atoi(argv[3]);  /* 1: skip FHZ-structural; 2: skip only calG; 0: skip none */
  init_edges(7); init_inc();
  memo=calloc(1u<<21,1); Gseen=calloc(1u<<21,1);
  FILE*f=fopen("g7.txt","r"); u32 F; int s,c; int idx=0;
  long repsY[8]={0}; long choicesY[8]={0}; int fails=0;
  while(fscanf(f,"%u %d %d",&F,&s,&c)==3){
    idx++;
    if(skipstruct==1 && s) continue;
    if(skipstruct==2 && c) continue;
    int done=0;
    for(int sz=7; sz>=5 && !done; sz--){
      for(int Y=0;Y<128 && !done;Y++) if(popc(Y)==sz){
        if(check_Y(F,Y,0)){
          long before=nchoices; check_Y(F,Y,1);
          repsY[sz]++; choicesY[sz]+=nchoices-before; done=1;
          printf("G %d mask %u struct %d calG %d Y %d size %d\n", idx, F, s, c, Y, sz);
        }
      }
    }
    if(!done){ fails++; printf("FAIL %d mask %u struct %d calG %d\n", idx, F, s, c); }
    fflush(stdout);
  }
  printf("SUMMARY DMAX=%d fails=%d\n",DMAX,fails);
  for(int sz=5;sz<=7;sz++) printf("|Y|=%d reps %ld choices %ld\n",sz,repsY[sz],choicesY[sz]);
  printf("choices total %ld  A-size0 %ld A-size1 %ld A-size2 %ld\n",nchoices,nchoicesA[0],nchoicesA[1],nchoicesA[2]);
  printf("distinct G %ld ; minimal |D| hist:",nG); for(int i=0;i<=DMAX;i++) printf(" %ld",dhist[i]); printf("\n");
  printf("win nodes %ld\n",NODES);
  return 0;
}
