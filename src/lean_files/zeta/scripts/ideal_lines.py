# B120: other ideal staircases from ln 3, ln 2. Per Order-n word (w_l = ones in the first l letters):
#  diag: sum_l |L w_l - l n| (area to the straight line from (0,0) to (L,n), Christoffel slope n/L), integer;
#  ruler: prod_l 3^(w_l)/2^l (the log-area above the ruler w = l log_3 2, the wall's line), rational;
#  maxdev: max_l |L w_l - l n|. Rank of the best (1 = smallest value) and how many words share its value.
import sys
from fractions import Fraction as F
T = lambda x: (3*x+1)//2 if x & 1 else x//2
p2 = lambda m: (3**m).bit_length()
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    L = p2(n); W = []
    for r in range(3, 2**L, 2):
        x = r; q = 0; ws = []
        for l in range(L):
            q += x & 1; x = T(x); ws.append(q)
            if 3**q < 2**(l+1): break
        if l == L-1 and q == n: W.append((F(x, r), r, ws))
    b = max(W)
    M = {'diag': lambda ws: sum(abs(L*w - (l+1)*n) for l, w in enumerate(ws)),
         'ruler': lambda ws: F(3**sum(ws), 2**(L*(L+1)//2)),
         'maxdev': lambda ws: max(abs(L*w - (l+1)*n) for l, w in enumerate(ws))}
    out = []
    for k, f in M.items():
        v = f(b[2]); vals = [f(t[2]) for t in W]
        out.append('%s rank %d (ties %d)' % (k, sum(1 for u in vals if u < v) + 1, sum(1 for u in vals if u == v) - 1))
    print('Order %d (%d words) best %d: %s' % (n, len(W), b[1], '; '.join(out)))
# clearance: the parallels of the ruler, 3^w = K 2^l; per word the lowest K over l < L (min 3^(w_l)/2^l),
# and the sum S = rho/3^n = sum over the ones of 2^k/3^q (each 1 weighted e^(-its ln-distance to the ruler)).
if len(sys.argv) > 3:
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        L = p2(n); W = []
        for r in range(3, 2**L, 2):
            x = r; q = 0; ws = []
            for l in range(L):
                q += x & 1; x = T(x); ws.append(q)
                if 3**q < 2**(l+1): break
            if l == L-1 and q == n: W.append((F(x, r), r, ws))
        b = max(W)
        cl = lambda ws: min(F(3**w, 2**(l+1)) for l, w in enumerate(ws[:-1]))
        v = cl(b[2]); vals = sorted(cl(t[2]) for t in W)
        print('Order %d best %d clearance %s, rank from top %d of %d distinct %d' % (n, b[1], v, sum(1 for u in vals if u > v) + 1, len(W), len(set(vals))))
