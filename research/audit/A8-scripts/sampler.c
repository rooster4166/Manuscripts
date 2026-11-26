/* random sampler: n vertices, target #even = e, optional: min degree, K_i-type T (two universal in T\{r} handled by caller) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n,A[16][16];
static int conn_wo(int rm){ int s=-1; for(int v=0;v<n;v++) if(!(rm>>v&1)){s=v;break;} int seen=1<<s,st[16],sp=0; st[sp++]=s;
  while(sp){int v=st[--sp]; for(int u=0;u<n;u++) if(A[v][u]&&!(rm>>u&1)&&!(seen>>u&1)){seen|=1<<u;st[sp++]=u;}}
  for(int v=0;v<n;v++) if(!(rm>>v&1)&&!(seen>>v&1)) return 0; return 1; }
static int bic(void){ for(int x=0;x<n;x++) if(!conn_wo(1<<x)) return 0; return conn_wo(0); }
int main(int argc,char**argv){
  n=atoi(argv[1]); int e=atoi(argv[2]); int count=atoi(argv[3]); int mindeg=atoi(argv[4]); unsigned seed=atoi(argv[5]); srand(seed);
  int got=0; long tries=0;
  while(got<count && tries<200000000L){ tries++;
    double p = 0.3 + 0.6*(rand()/(double)RAND_MAX);
    memset(A,0,sizeof A);
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(rand()/(double)RAND_MAX<p) A[i][j]=A[j][i]=1;
    int ne=0, md=99; for(int v=0;v<n;v++){int d=0; for(int u=0;u<n;u++) d+=A[v][u]; if(d%2==0) ne++; if(d<md) md=d;}
    if(ne!=e || md<mindeg) continue; if(!bic()) continue;
    char out[64]; out[0]=63+n; int val=0,bits=0,p2=1;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|A[i][j]; bits++; if(bits==6){ out[p2++]=63+val; val=0; bits=0; } }
    if(bits){ val<<=(6-bits); out[p2++]=63+val; } out[p2]=0; puts(out); got++; }
  fprintf(stderr,"got %d tries %ld\n",got,tries);
}
