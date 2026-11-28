/* A42: uniform random sample of joined L_N(2) instances (or separated with argv[3]=S) over a graph6
   list: each instance is kept independently with probability p = argv[1]; seed argv[2].
   Output: 'g6 J c1 c2 A c1 a1 A c2 a2' (joined) or 'g6 c1 a1 c2 a2' (separated). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int n; static unsigned adj[32];
static void dec(const char*s){ n=s[0]-63; int bit=0,cur=0; const char*p=s+1; memset(adj,0,sizeof adj);
  for(int j=1;j<n;j++)for(int i=0;i<j;i++){ if(!bit){cur=*p++-63;bit=6;} bit--; if(cur>>bit&1){adj[i]|=1u<<j;adj[j]|=1u<<i;} } }
static unsigned comp(int s,unsigned banned){unsigned seen=1u<<s,fr=seen;while(fr){int x=__builtin_ctz(fr);fr&=fr-1;unsigned nb=adj[x]&~seen&~banned;seen|=nb;fr|=nb;}return seen;}
static uint64_t st=88172645463325252ULL; static double rnd(void){ st^=st<<13; st^=st>>7; st^=st<<17; return (st>>11)*(1.0/9007199254740992.0); }
int main(int argc,char**argv){ double p=atof(argv[1]); st^=(uint64_t)atoll(argv[2])*0x9E3779B97F4A7C15ULL; int sep=argc>3;
  char line[256]; while(fgets(line,sizeof line,stdin)){ line[strcspn(line,"\r\n")]=0; if(!line[0]) continue; dec(line);
    int P[200][2],np=0; for(int c=0;c<n;c++)for(int a=0;a<n;a++) if(c!=a&&!(adj[c]>>a&1)){P[np][0]=c;P[np][1]=a;np++;}
    for(int i=0;i<np;i++)for(int j=i+1;j<np;j++){ int c1=P[i][0],a1=P[i][1],c2=P[j][0],a2=P[j][1];
      if(c1==c2||c1==a2||a1==c2||a1==a2) continue;
      int joined = comp(c1,(1u<<a1)|(1u<<a2))>>c2&1;
      if(joined==sep) continue;
      if(rnd()>=p) continue;
      if(joined) printf("%s J %d %d A %d %d A %d %d\n",line,c1,c2,c1,a1,c2,a2); else printf("%s %d %d %d %d\n",line,c1,a1,c2,a2); } }
  return 0; }
