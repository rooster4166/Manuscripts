#include "pn.h"
int main(int argc,char**argv){ char line[256]; int adj[16][16];
  while(fgets(line,sizeof line,stdin)){ line[strcspn(line,"\n")]=0; int n=g6decode(line,adj); pn_setgraph(n,adj);
    int b=0; while(1){ int r=pn_le(b); if(r==1) break; if(r<0){ b=-1; break;} b++; } printf("%s %d\n",line,b); }
}
