// a41odd.cpp: keep connected graphs (graph6 on stdin) in which every degree is odd.
#include <bits/stdc++.h>
int main(){ char s[256]; while (fgets(s,sizeof s,stdin)) { int n=(unsigned char)s[0]-63; unsigned A[16]={0};
  int k=1,bit=0,cur=0; for(int j=1;j<n;j++)for(int i=0;i<j;i++){ if(!bit){cur=(unsigned char)s[k++]-63;bit=6;} bit--; if(cur>>bit&1){A[i]|=1u<<j;A[j]|=1u<<i;} }
  bool ok=true; for(int v=0;v<n;v++) if(!(__builtin_popcount(A[v])&1)) ok=false; if(!ok) continue;
  unsigned c=1,fr=1; while(fr){int x=__builtin_ctz(fr);fr&=fr-1;unsigned nb=A[x]&~c;c|=nb;fr|=nb;} if(c!=(1u<<n)-1) continue; fputs(s,stdout);} }
