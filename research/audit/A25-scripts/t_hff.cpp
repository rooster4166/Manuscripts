// t_hff.cpp: the order-9 instance H??FFf} of tight-fan (Lemma 3.2 remark), replayed with the a25 chain.
#include "a25.h"
using namespace a25;
int main(){ Graph G; decode_g6("H??FFf}", G); Graph H=G; H.rem(3,7);
 Dec D={{8,2,7,0,6},{0,8,4},{5,8,1,6,2},{1,7,6,8,3}}; Dec D2; std::vector<int> ch;
 printf("D' valid for G-37: %d\n",(int)check(H,D)); forced_chain(D,3,7,D2,ch);
 printf("chain:"); for(int x:ch) printf(" %d",x); printf("  image %s valid %d Q_0=", dstr(D2).c_str(), (int)check(G,D2));
 for(int x: D2[path_ending_at(D2,0)]) printf("%d",x); printf("\n"); }
