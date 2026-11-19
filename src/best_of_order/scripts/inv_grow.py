# B120: grow the inverse tree of a hub h (predecessors 2y and (2y-1)/3 when odd), values below 2^V, and per
# odd node c < 2^C (c > h) its drop (first T^L(c) < c), Order n (ones up to the drop) and ratio T^L(c)/c.
# Per Order: the best inside the tree against the global best (boo_75/76.out). Usage: inv_grow.py h V C
import sys, time
from fractions import Fraction as F
h, V, C = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
B = {}
for f in ('boo_75.out', 'boo_76.out'):
    for line in open(f):
        a = line.split()
        if a and a[0].isdigit(): B[int(a[0])] = int(a[1])
t0 = time.time(); top = 2**V; seen = {h}; st = [h]
while st:
    y = st.pop()
    for x in (2*y, (2*y-1)//3 if (2*y-1) % 3 == 0 and ((2*y-1)//3) & 1 else 0):
        if 1 < x < top and x not in seen: seen.add(x); st.append(x)
best = {}
for c in seen:
    if not c & 1 or c >= 2**C: continue
    x = c; n = 0
    while x >= c:
        if x & 1: n += 1; x = (3*x+1)//2
        else: x //= 2
    q = F(x, c)
    if n not in best or q > best[n][0]: best[n] = (q, c)
hit = [n for n in sorted(best) if B.get(n) == best[n][1]]
print('hub %d: %d nodes below 2^%d, %.1fs; Orders whose global best is in the tree: %d: %s' % (h, len(seen), V, time.time()-t0, len(hit), hit))
