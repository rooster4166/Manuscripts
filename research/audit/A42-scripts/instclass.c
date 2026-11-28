/* A42: count L_N(2) instances (unordered pair of disjoint ordered pairs (c1,a1),(c2,a2), c_i !~ a_i,
   four distinct vertices) over a graph6 list; split joined / separated; classify separated ones:
   B  (Cor. B of ln: some c_i a leaf with a_i not in N[stem], no vertex adjacent to both a1, a2),
   G  (Theorem 7.1, (G1)-(G3) with the NA clause), Gn (same without the NA clause: (G3) only c_i !~ v),
   leaf (c_i a leaf whose only neighbour is a_j), cut (a_1 or a_2 alone separates), 2cut.
   Precedence as in the manuscript's Section 7 list: B, G, leaf, cut, 2cut.
   Also counts: AEq = separated, not B, not Gn, leaf (the AE queries); CR = separated, not B, not Gn,
   not leaf (the Criterion R run).  Optional argv[1]: file to write separated instances to. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static int n; static unsigned adj[32];
static int dec(const char *s){ n=s[0]-63; int k=0,bit=0,cur=0; const char*p=s+1; memset(adj,0,sizeof adj);
  for(int j=1;j<n;j++)for(int i=0;i<j;i++){ if(!bit){cur=*p++-63;bit=6;} bit--; if(cur>>bit&1){adj[i]|=1u<<j;adj[j]|=1u<<i;} k++;} return 1;}
static unsigned comp(int s, unsigned banned){ unsigned seen=1u<<s, fr=1u<<s; while(fr){int x=__builtin_ctz(fr); fr&=fr-1; unsigned nb=adj[x]&~seen&~banned; seen|=nb; fr|=nb;} return seen;}
static int deg(int v){return __builtin_popcount(adj[v]);}
static int corB(int c1,int a1,int c2,int a2){
  for(int x=0;x<n;x++) if((adj[x]>>a1&1)&&(adj[x]>>a2&1)) return 0;
  int c[2]={c1,c2}, a[2]={a1,a2};
  for(int t=0;t<2;t++) if(deg(c[t])==1){ int w=__builtin_ctz(adj[c[t]]); if(a[t]!=w && !(adj[w]>>a[t]&1)) return 1; }
  return 0;}
/* gluing for orientation (ci,ai,cj,aj); na=1 with the NA clause */
static int glue(int ci,int ai,int cj,int aj,int na){
  int v=aj; unsigned B=comp(cj,1u<<v);
  if(B>>ci&1) return 0;
  if(!(B>>ai&1)) return 1;
  if(__builtin_popcount(adj[v]&B)%2) return 1;
  if(!(adj[v]>>ci&1)) return 1;
  if(!na) return 0;
  unsigned C=comp(ci,1u<<v);
  return (C & ~adj[v]) != 0;
}
int main(int argc,char**argv){
  FILE*fs = argc>1? fopen(argv[1],"w"):NULL;
  char line[256]; long tot=0,joined=0,sep=0,cB=0,cG=0,cL=0,cC=0,c2=0,AEq=0,CR=0,Gn=0,leafany=0;
  while(fgets(line,sizeof line,stdin)){ line[strcspn(line,"\r\n")]=0; if(!line[0]) continue; dec(line);
    int P[200][2], np=0;
    for(int c=0;c<n;c++)for(int a=0;a<n;a++) if(c!=a && !(adj[c]>>a&1)){P[np][0]=c;P[np][1]=a;np++;}
    for(int i=0;i<np;i++)for(int j=i+1;j<np;j++){
      int c1=P[i][0],a1=P[i][1],c2_=P[j][0],a2=P[j][1];
      if(c1==c2_||c1==a2||a1==c2_||a1==a2) continue;
      tot++;
      unsigned R=comp(c1,(1u<<a1)|(1u<<a2));
      if(R>>c2_&1){joined++; continue;}
      sep++; if(fs) fprintf(fs,"%s %d %d %d %d\n",line,c1,a1,c2_,a2);
      int b=corB(c1,a1,c2_,a2);
      int g=glue(c1,a1,c2_,a2,1)||glue(c2_,a2,c1,a1,1);
      int gn=glue(c1,a1,c2_,a2,0)||glue(c2_,a2,c1,a1,0);
      int lf=(deg(c1)==1 && (adj[c1]>>a2&1)) || (deg(c2_)==1 && (adj[c2_]>>a1&1));
      int cut=!(comp(c1,1u<<a1)>>c2_&1) || !(comp(c1,1u<<a2)>>c2_&1);
      if(b) cB++; else if(g) cG++; else if(lf) cL++; else if(cut) cC++; else c2++;
      if(!b && gn) Gn++;
      if(!b && !gn && lf) AEq++;
      if(!b && !gn && !lf) CR++;
    }
  }
  printf("instances %ld joined %ld separated %ld | B %ld G %ld leaf %ld cut %ld 2cut %ld | notB&Gn %ld AEqueries %ld CriterionR-run %ld\n",
    tot,joined,sep,cB,cG,cL,cC,c2,Gn,AEq,CR);
  if(fs) fclose(fs); return 0;}
