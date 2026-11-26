/* Export Thm 124 certificates found by seven.c logic, with explicit restoration trees. */
#include "fan.h"
static int DMAX=5;
static unsigned char *memo; static u32 *memoD;
/* tree writer: same search as win() but records the first winning (w,S) */
static FILE *OUT;
static int wintree(u32 G,u32 M,int*b,char*buf,int*pos){
  if(!M){ *pos+=sprintf(buf+*pos,"L"); return 1; }
  u32 cur=G&~M;
  for(int w=0;w<NV;w++){
    u32 mw=M&INC[w]; if(!mw) continue;
    int cand[8],nc=0; for(u32 m=mw;m;m&=m-1){int e=__builtin_ctz(m);int t=EU[e]==w?EV[e]:EU[e]; if(b[t]>0) cand[nc++]=t;}
    if(!nc) continue;
    int z=0; for(u32 m=cur&INC[w];m;m&=m-1){int e=__builtin_ctz(m);int x=EU[e]==w?EV[e]:EU[e]; if(b[x]==0) z++;}
    for(int S=1;S<(1<<nc);S++){
      int sum=0; for(int i=0;i<nc;i++) if(S>>i&1) sum+=b[cand[i]];
      if(sum<=z) continue;
      int dom=0; for(int i=0;i<nc&&!dom;i++) if(S>>i&1) if(sum-b[cand[i]]>z) dom=1; if(dom) continue;
      int save=*pos; *pos+=sprintf(buf+*pos,"(%d:",w); int ok=1;
      for(int i=0;i<nc&&ok;i++) if(S>>i&1){ int t=cand[i]; int e=EIDX[w][t];
        *pos+=sprintf(buf+*pos,"[%d ",t); b[w]++; b[t]--; ok=wintree(G,M&~(1u<<e),b,buf,pos); b[w]--; b[t]++; *pos+=sprintf(buf+*pos,"]"); }
      if(ok){ *pos+=sprintf(buf+*pos,")"); return 1; }
      *pos=save; buf[save]=0;
    }
  }
  return 0;
}
static int certifiable(u32 G,u32*Dfound){
  if(memo[G]){ *Dfound=memoD[G]; return memo[G]!=255; }
  int edges[21],ne=0; for(u32 m=G;m;m&=m-1) edges[ne++]=__builtin_ctz(m);
  for(int ds=0;ds<=DMAX&&ds<=ne;ds++){
    int c[8]; for(int i=0;i<ds;i++) c[i]=i;
    while(1){ u32 D=0; for(int i=0;i<ds;i++) D|=1u<<edges[c[i]];
      int b[8],Z=0; for(int v=0;v<NV;v++){b[v]=popc(D&INC[v])&1; if(!b[v]) Z|=1<<v;}
      if(is_forest(G&~D,Z)&&win(G,D,b)){memo[G]=1;memoD[G]=D;*Dfound=D;return 1;}
      int i=ds-1; while(i>=0&&c[i]==ne-ds+i) i--; if(i<0) break; c[i]++; for(int j=i+1;j<ds;j++) c[j]=c[j-1]+1; }
  }
  memo[G]=255; return 0;
}
static u32 paths[400]; static int plen[400]; static int npaths;
static void dfs(u32 F,int Y,int cur,int q,int vis,u32 em,int len){
  if(cur==q){paths[npaths]=em;plen[npaths]=len;npaths++;return;}
  for(int v=0;v<NV;v++) if(((Y>>v)&1)&&!((vis>>v)&1)&&(F>>EIDX[cur][v]&1)) dfs(F,Y,v,q,vis|(1<<v),em|(1u<<EIDX[cur][v]),len+1);
}
static int cmpfun(const void*a,const void*b){int x=*(int*)a,y=*(int*)b; return plen[y]-plen[x];}
static int nA; static u32 Aset[64];
static void addA(u32 a){for(int i=0;i<nA;i++) if(Aset[i]==a) return; Aset[nA++]=a;}
static void gen_lists(u32 F,int p,int q,int*O,int n){
  nA=0; int pw=1; for(int i=0;i<n;i++) pw*=3;
  for(int code=0;code<pw;code++){ int a1[3],n1=0,a2[3],n2=0,c=code;
    for(int i=0;i<n;i++){int t=c%3;c/=3; if(t==1)a1[n1++]=O[i]; else if(t==2)a2[n2++]=O[i];}
    for(int s1=0;s1<(n1==2?2:1);s1++) for(int s2=0;s2<(n2==2?2:1);s2++){
      int l1[3],l2[3],m1=0,m2=0; l1[m1++]=p; l2[m2++]=q;
      for(int i=0;i<n1;i++) l1[m1++]=a1[s1?n1-1-i:i]; for(int i=0;i<n2;i++) l2[m2++]=a2[s2?n2-1-i:i];
      u32 cand=0; for(int i=0;i+1<m1;i++){int e=EIDX[l1[i]][l1[i+1]]; if(F>>e&1) cand|=1u<<e;}
      for(int i=0;i+1<m2;i++){int e=EIDX[l2[i]][l2[i+1]]; if(F>>e&1) cand|=1u<<e;}
      for(u32 s=cand;;s=(s-1)&cand){addA(s); if(!s) break;} } }
}
static char buf[1<<20];
static int check_Y(u32 F,int Y,int emit){
  int O[7],no=0; for(int v=0;v<NV;v++) if(!((Y>>v)&1)) O[no++]=v;
  for(int p=0;p<NV;p++) if((Y>>p)&1) for(int q=p+1;q<NV;q++) if((Y>>q)&1){
    gen_lists(F,p,q,O,no); npaths=0; dfs(F,Y,p,q,1<<p,0,0);
    int ord[400]; for(int i=0;i<npaths;i++) ord[i]=i; qsort(ord,npaths,sizeof(int),cmpfun);
    for(int ai=0;ai<nA;ai++){ u32 A=Aset[ai]; int found=0;
      for(int k=0;k<npaths&&!found;k++){ u32 G=F&~A&~paths[ord[k]]; u32 D;
        if(certifiable(G,&D)){ found=1;
          if(emit){ int b[8]; for(int v=0;v<NV;v++) b[v]=popc(D&INC[v])&1; int pos=0; buf[0]=0; wintree(G,D,b,buf,&pos);
            fprintf(OUT,"C %d %d %u %u %u %s\n",p,q,A,paths[ord[k]],D,buf); } } }
      if(!found) return 0; } }
  return 1;
}
int main(){
  init_edges(7); init_inc(); memo=calloc(1u<<21,1); memoD=calloc(1u<<21,4);
  FILE*f=fopen("g7.txt","r"); OUT=fopen("cert124.txt","w"); u32 F; int s,c;
  while(fscanf(f,"%u %d %d",&F,&s,&c)==3){
    if(s){ fprintf(OUT,"S %u\n",F); continue; }
    int done=0;
    for(int sz=7;sz>=5&&!done;sz--) for(int Y=0;Y<128&&!done;Y++) if(popc(Y)==sz && check_Y(F,Y,0)){ fprintf(OUT,"F %u %d\n",F,Y); check_Y(F,Y,1); done=1; }
    if(!done) fprintf(OUT,"X %u\n",F);
  }
  fclose(OUT); return 0;
}
