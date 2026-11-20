# The number of words of Order n (A100982), counted exactly by (ones, letters), and the words of one
# Order with their constant rho, class id c, drop value d and rho/c (Chapter 2 of the best paper).
# Usage: python3 boo_count.py N1 N2      counts for Orders N1..N2 (and their number of digits)
#        python3 boo_count.py --words n  the words of Order n, best first
import sys
from fractions import Fraction

def p2(n): return (3 ** n).bit_length()

def count(n):                       # prefixes by their number of ones; nonempty proper ones need 3^j > 2^l
    L = p2(n); cur = {0: 1}
    for l in range(1, L + 1):
        nxt = {}
        for j, v in cur.items():
            for j2 in (j, j + 1):
                if j2 > n or (l < L and 3 ** j2 <= 2 ** l): continue
                nxt[j2] = nxt.get(j2, 0) + v
        cur = nxt
    return cur.get(n, 0)

def words(n):
    L = p2(n); out = []
    def go(w, j):
        l = len(w)
        if l == L:
            if j == n: out.append(w)
            return
        for e in '01':
            j2 = j + int(e)
            if j2 > n or (l + 1 < L and 3 ** j2 <= 2 ** (l + 1)): continue
            go(w + e, j2)
    go('', 0)
    return out

if sys.argv[1] == '--words':
    n = int(sys.argv[2]); L = p2(n); rows = []
    for w in words(n):
        ks = [i for i, e in enumerate(w) if e == '1']
        rho = sum(3 ** (n - q) * 2 ** k for q, k in enumerate(ks, 1))
        r = -rho * pow(3, -n, 2 ** L) % 2 ** L
        c = r if r > 1 else r + 2 ** L
        d, m = divmod(3 ** n * c + rho, 2 ** L); assert m == 0
        rows.append((Fraction(rho, c), w, rho, c, d))
    for f, w, rho, c, d in sorted(rows, reverse=True):
        print(w, 'rho', rho, 'c', c, 'd', d, 'rho/c', f)
else:
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        k = count(n); print(n, k, len(str(k)))
