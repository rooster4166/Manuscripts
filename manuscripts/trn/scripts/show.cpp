// show.cpp: for given g6 g y x u, list every good D' of G-gu with its chain and image.
#include "dec.h"
using namespace dec;
static void pp(const Path& p) { for (size_t i = 0; i < p.size(); i++) printf("%d", p[i]); }
int main(int argc, char** argv) {
  Gr G; parse_g6(argv[1], G); int g = atoi(argv[2]), y = atoi(argv[3]), x = atoi(argv[4]), u = atoi(argv[5]);
  Gr H = G; H.del(g, u);
  printf("G: "); print_edges(stdout, G); printf("\n");
  enumerate(H, y, 1u << x, 0, [&](const Decomp& D) {
    std::vector<int> ch; Decomp R = fan_forced(D, g, u, ch);
    bool hit = std::find(ch.begin(), ch.end(), y) != ch.end();
    bool ok = path_avoids(R[path_end_at(R, y)], 1u << x);
    printf("%s D'={", hit ? (ok ? "HIT-ok " : "HIT-BAD") : "avoid  ");
    for (auto& p : D) { pp(p); printf(" "); } printf("} chain=");
    for (int v : ch) printf("%d", v); printf(" image={");
    for (auto& p : R) { pp(p); printf(" "); } printf("} Q(y)="); pp(R[path_end_at(R, y)]); printf("\n");
    return false; });
}
