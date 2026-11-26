/* Local certificate searches: (a) MR p.131 K_i seven-site table; (b) MR Lemma 133 boundary table. */
#include "fan.h"
static int DMAX=8;
static const char *SH[]={"ab ac ad ae bc bd be","ab ac ad ae bc bd be cd","ab ac ad ae bc bd be cd de","ab ac ad ae bc bd be cd de ce",
  "ab ac ad ae bc de","ab ac ad ae bc cd de","ab ac ad ae bc cd de eb"};
static const char *SHN[]={"K0","K1","K2","K3","M","P","C"};
static u32 shape_mask(int s){ u32 m=0; const char*p=SH[s]; while(*p){ if(*p==' '){p++;continue;} int a=p[0]-'a',b=p[1]-'a'; m|=1u<<EIDX[a][b]; p+=2; } return m; }
static int search(u32 G, int *orig, int mode, int *dsize, u32 *Dout){
  int edges[28],ne=0; for(u32 m=G;m;m&=m-1) edges[ne++]=__builtin_ctz(m);
  for(int ds=0; ds<=DMAX && ds<=ne; ds++){
    int c[12]; for(int i=0;i<ds;i++) c[i]=i;
    while(1){
      u32 D=0; for(int i=0;i<ds;i++) D|=1u<<edges[c[i]];
      int par[8], ev[8], nev=0;
      for(int v=0;v<NV;v++){ par[v]=orig[v]^(popc(D&INC[v])&1); if(!par[v]) ev[nev++]=v; }
      int b[8];
      if(mode==0){ /* K_i: exactly one even site */
        if(nev==1){ for(int v=0;v<NV;v++) b[v]=par[v]?1:0; LEAFMODE=0; if(win(G,D,b)){*dsize=ds;*Dout=D;return 1;} }
      } else { /* Lemma 133: 0 or 2 even; y = vertex 5 needs >=2 at leaves */
        LEAFMODE=1; LEAFV=5; LEAFMIN=2;
        if(nev==0){ for(int v=0;v<NV;v++) b[v]=1; if(win(G,D,b)){*dsize=ds;*Dout=D;return 1;} }
        else if(nev==2){
          for(int k=0;k<2;k++){ int p=ev[k], pp=ev[1-k];
            if(!((G&~D)&INC[p])) continue; /* designated site needs a retained edge */
            for(int v=0;v<NV;v++) b[v]=1; b[p]=2; b[pp]=0;
            if(win(G,D,b)){*dsize=ds;*Dout=D;return 1;} }
        }
      }
      int i=ds-1; while(i>=0 && c[i]==ne-ds+i) i--; if(i<0) break; c[i]++; for(int j=i+1;j<ds;j++) c[j]=c[j-1]+1;
    }
  }
  return 0;
}
int main(int argc,char**argv){
  if(argc>1) DMAX=atoi(argv[1]);
  init_edges(7); init_inc();
  /* (a) K_i table: sites a..e = 0..4, u=5, v=6 */
  printf("K_i seven-site table (u=5 sees A, uv edge, v misses K):\n");
  for(int s=0;s<4;s++){
    int covered=0; char rem[400]=""; int hist[12]={0};
    for(int A=1;A<32;A++){
      u32 G=shape_mask(s); for(int x=0;x<5;x++) if(A>>x&1) G|=1u<<EIDX[5][x]; G|=1u<<EIDX[5][6];
      int orig[8]={0,0,0,0,0,1,1,0}; int ds; u32 D;
      if(search(G,orig,0,&ds,&D)){ covered++; hist[ds]++; }
      else { char t[8]; int k=0; for(int x=0;x<5;x++) if(A>>x&1) t[k++]='a'+x; t[k]=0; strcat(rem,t); strcat(rem," "); }
    }
    printf("  %s covered %d of 31; uncovered: %s ; minimal|D| hist:",SHN[s],covered,rem); for(int i=0;i<=DMAX;i++) printf(" %d",hist[i]); printf("\n");
  }
  /* (b) Lemma 133 boundary table: T = 0..4 shape M/P/C, y = 5, vertex 6 unused */
  init_edges(6); init_inc();
  printf("Lemma 133 boundary table (y=5 sees N, T in {M,P,C}):\n");
  for(int s=4;s<7;s++){
    /* rebuild shape mask with 6-vertex indexing */
    int covered=0; char rem[400]=""; int hist[12]={0};
    for(int N=1;N<32;N++){
      u32 G=shape_mask(s); for(int x=0;x<5;x++) if(N>>x&1) G|=1u<<EIDX[5][x];
      int orig[8]={0,0,0,0,0,0,0,0}; int ds; u32 D;
      if(search(G,orig,1,&ds,&D)){ covered++; hist[ds]++; }
      else { char t[8]; int k=0; for(int x=0;x<5;x++) if(N>>x&1) t[k++]='a'+x; t[k]=0; strcat(rem,t); strcat(rem," "); }
    }
    printf("  %s covered %d of 31; uncovered: %s ; minimal|D| hist:",SHN[s],covered,rem); for(int i=0;i<=DMAX;i++) printf(" %d",hist[i]); printf("\n");
  }
  printf("win nodes %ld\n",NODES);
}
