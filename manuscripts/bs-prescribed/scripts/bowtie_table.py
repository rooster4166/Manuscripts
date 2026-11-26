"""Print the bowtie certificates for the 11 orbit representatives of the contact set A
(rim ab, cd; labels x=0, a=1, b=2, c=3, d=4, u=5, v=6), with (supply, blanks) at every move.
Output is the table of Section 5 of the manuscript."""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
NM = 'xabcduv'
REPS = ['x', 'a', 'ab', 'ac', 'abc', 'abcd', 'xa', 'xab', 'xac', 'xabc', 'xabcd']


def show(c):
    E = {tuple(sorted(e)) for e in c['E']}
    H = [tuple(sorted(h)) for h in c['H']]
    out = []

    def walk(t, ins, cv, pre):
        if t[0] == 'done':
            S = ''.join(NM[i] for i in range(5) if cv[i] == 2)
            out.append(pre + f' => S={S}')
            return
        _, ds, r, kids = t
        present = (E - set(H)) | ins
        blank = sum(1 for a in range(7) if a != r and tuple(sorted((a, r))) in present and cv[a] == 0)
        sup = sum(cv[d] for d in ds)
        mv = ('{' + ','.join(NM[d] for d in ds) + '}' if len(ds) > 1 else NM[ds[0]]) + '->' + NM[r]
        for d in ds:
            if cv[d] == 0:
                continue
            nc = list(cv); nc[d] -= 1; nc[r] += 1
            tag = f'[{NM[d]}]' if len(ds) > 1 else ''
            walk(kids[str(d)], ins | {tuple(sorted((d, r)))}, nc, pre + f' {mv}{tag}({sup}>{blank})')

    walk(c['tree'], set(), list(c['c0']), '')
    return H, c['c0'].index(0), out


bow = json.load(open(os.path.join(HERE, 'certs_bowtie.json')))
for rep in REPS:
    Acode = sum(1 << 'xabcd'.index(ch) for ch in rep)
    c = next(c for c in bow if c['code'] == 33 and c['Acode'] == Acode)
    H, z, lines = show(c)
    print(f"A={rep:6s} hold {' '.join(NM[a]+NM[b] for a,b in H):18s} seed-even {NM[z]}")
    for l in lines:
        print('     ', l)
