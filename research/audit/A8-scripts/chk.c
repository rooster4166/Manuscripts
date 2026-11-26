#include "pn.h"
static int n; static int adj[16][16];
static int deg(int v){ int d=0; for(int u=0;u<n;u++) d+=adj[v][u]; return d; }
static int connected_without(int N_, int A_[16][16], int rm){ /* rm = bitmask of removed vertices */
  int s=-1; for(int v=0;v<N_;v++) if(!(rm>>v&1)){s=v;break;} if(s<0) return 1;
  int seen=1<<s, st[16], sp=0; st[sp++]=s;
  while(sp){ int v=st[--sp]; for(int u=0;u<N_;u++) if(A_[v][u] && !(rm>>u&1) && !(seen>>u&1)){ seen|=1<<u; st[sp++]=u; } }
  for(int v=0;v<N_;v++) if(!(rm>>v&1) && !(seen>>v&1)) return 0; return 1; }
static int kconn(int N_, int A_[16][16], int k){ /* k in {2,3} */
  if(N_<=k) return 0;
  for(int x=0;x<N_;x++){ if(!connected_without(N_,A_,1<<x)) return 0;
    if(k==3) for(int y=x+1;y<N_;y++) if(!connected_without(N_,A_,(1<<x)|(1<<y))) return 0; }
  return connected_without(N_,A_,0); }
static int W[16][16];
static int solve_with_leaves(int *roots,int nr,int budget){
  memcpy(W,adj,sizeof W); int N_=n;
  for(int i=0;i<nr;i++){ W[roots[i]][N_]=W[N_][roots[i]]=1; N_++; }
  pn_setgraph(N_,W); return pn_le(budget);
}
static long cnt[20][20], fail[20][20], abrt[20][20];
int main(int argc,char**argv){
  const char*mode=argv[1]; char line[256]; long ngr=0;
  while(fgets(line,sizeof line,stdin)){ line[strcspn(line,"\n")]=0; if(!line[0]) continue; n=g6decode(line,adj);
    int even[16],ne=0; for(int v=0;v<n;v++) if(deg(v)%2==0) even[ne++]=v; if(argc>2 && atoi(argv[2]) && ne!=atoi(argv[2])) continue;
    if(!strcmp(mode,"testi")){ if(n%2) continue; if(ne<4) continue;
      int J[16][16]; memcpy(J,adj,sizeof J); for(int i=0;i<16;i++){J[n][i]=J[i][n]=0;} for(int i=0;i<ne;i++) J[n][even[i]]=J[even[i]][n]=1;
      if(!kconn(n+1,J,3)) continue; ngr++;
      for(int i=0;i<ne;i++){ int r=even[i]; int res=solve_with_leaves(&r,1,n/2); int d=ne, dr=deg(r);
        cnt[d][dr]++; if(res==0){fail[d][dr]++; printf("FAIL testi %s r=%d d=%d dB(r)=%d\n",line,r,d,dr);} if(res<0){abrt[d][dr]++; printf("ABORT %s r=%d\n",line,r);} } }
    else if(!strcmp(mode,"testii")){ if(n%2==0) continue; if(ne<3) continue;
      for(int r=0;r<n;r++) if(deg(r)%2==1){
        int J[16][16]; memcpy(J,adj,sizeof J); for(int i=0;i<16;i++){J[n][i]=J[i][n]=0;} for(int i=0;i<ne;i++) J[n][even[i]]=J[even[i]][n]=1; J[n][r]=J[r][n]=1;
        if(!kconn(n+1,J,3)) continue; ngr++;
        int rr[2]={r,r}; int res=solve_with_leaves(rr,2,(n+1)/2); int d=ne+1, dr=deg(r);
        cnt[d][dr]++; if(res==0){fail[d][dr]++; printf("FAIL testii %s r=%d d=%d dB(r)=%d\n",line,r,d,dr);} if(res<0){abrt[d][dr]++; printf("ABORT %s r=%d\n",line,r);} } }
    else if(!strcmp(mode,"t124")){ if(n%2==0) continue; if(ne<2||ne>9) continue; if(!kconn(n,adj,2)) continue; ngr++;
      for(int i=0;i<ne;i++) for(int j=i+1;j<ne;j++){ int rr[2]={even[i],even[j]}; int res=solve_with_leaves(rr,2,(n+1)/2);
        cnt[ne][0]++; if(res==0){fail[ne][0]++; printf("FAIL t124 %s u=%d h=%d\n",line,rr[0],rr[1]);} if(res<0){abrt[ne][0]++; printf("ABORT %s\n",line);} } }
    else if(!strcmp(mode,"t128")){ if(n%2==0) continue; if(ne>7) continue; if(!kconn(n,adj,2)) continue; ngr++;
      for(int r=0;r<n;r++) if(deg(r)%2==1 && deg(r)>=3){ int rr[2]={r,r}; int res=solve_with_leaves(rr,2,(n+1)/2); int dr=deg(r);
        cnt[ne][dr]++; if(res==0){fail[ne][dr]++; printf("FAIL t128 %s r=%d\n",line,r);} if(res<0){abrt[ne][dr]++; printf("ABORT %s\n",line);} } }
    else if(!strcmp(mode,"l126")){ if(n%2==0) continue;
      for(int r=0;r<n;r++) if(deg(r)%2==1 && deg(r)>=3){ if(!connected_without(n,adj,1<<r)) continue;
        int Z[16],nz=0; for(int i=0;i<ne;i++) if(!adj[r][even[i]]) Z[nz++]=even[i];
        int ok=1; for(int i=0;i<nz;i++){ int dz=0; for(int j=0;j<nz;j++) dz+=adj[Z[i]][Z[j]]; if(dz>3) ok=0; } if(!ok) continue; ngr++;
        int rr[2]={r,r}; int res=solve_with_leaves(rr,2,(n+1)/2); int dr=ne-nz;
        cnt[ne][dr]++; if(res==0){fail[ne][dr]++; printf("FAIL l126 %s r=%d\n",line,r);} if(res<0){abrt[ne][dr]++; printf("ABORT %s\n",line);} } }
    else if(!strcmp(mode,"beven")){ if(n%2) continue; if(!kconn(n,adj,2)) continue; ngr++;
      for(int i=0;i<ne;i++){ int r=even[i]; int res=solve_with_leaves(&r,1,n/2); int dr=deg(r);
        cnt[ne][dr]++; if(res==0){fail[ne][dr]++; printf("FAIL beven %s r=%d e=%d d=%d\n",line,r,ne,dr);} if(res<0){abrt[ne][dr]++; printf("ABORT %s\n",line);} } }
  }
  printf("SUMMARY mode=%s graphs=%ld\n",mode,ngr);
  for(int a=0;a<20;a++) for(int b=0;b<20;b++) if(cnt[a][b]) printf("  [%s %d, %s %d] instances %ld fails %ld aborts %ld\n", (!strcmp(mode,"t124")||!strcmp(mode,"t128")||!strcmp(mode,"beven")||!strcmp(mode,"l126"))?"#even":"d", a, "deg(r)", b, cnt[a][b], fail[a][b], abrt[a][b]);
}
