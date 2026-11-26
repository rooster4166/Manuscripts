#include "pn.h"
/* print p(G+leaf r) for even r, p(G+2 leaves) for odd r deg>=3, and p(G + leaf u + leaf h) for even pairs */
int main(){ char line[256]; int adj[16][16], W[16][16];
  while(fgets(line,sizeof line,stdin)){ line[strcspn(line,"\n")]=0; int n=g6decode(line,adj);
    for(int r=0;r<n;r++){ int d=0; for(int u=0;u<n;u++) d+=adj[r][u];
      memcpy(W,adj,sizeof W); int N=n; int k = (d%2==0)?1:2; if(d%2==1 && d<3) continue; if(d==0) continue;
      for(int i=0;i<k;i++){ W[r][N]=W[N][r]=1; N++; }
      pn_setgraph(N,W); int b=0; while(pn_le(b)!=1) b++; printf("%s %d %d %d\n",line,r,(d%2==0)?2:3,b); } }
}
