# B120: inverse trees. Per Order n, all class ids c (3 <= c < 2^L) with their drop d = T^L(c) and o = odd part of d.
# How does the best's o compare: its size rank among the o's, the number of words per o, the best within each o.
import sys
from fractions import Fraction as F
from collections import defaultdict
T = lambda x: (3*x+1)//2 if x & 1 else x//2
p2 = lambda m: (3**m).bit_length()
odd = lambda x: x >> ((x & -x).bit_length() - 1)
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    L = p2(n); W = []
    for r in range(3, 2**L, 2):
        x = r; q = 0
        for l in range(L):
            q += x & 1; x = T(x)
            if 3**q < 2**(l+1): break
        if l == L-1 and q == n: W.append((F(x, r), r, x))
    W.sort(reverse=True); b = W[0]
    G = defaultdict(list)
    for t in W: G[odd(t[2])].append(t)
    os_ = sorted(G); ob = odd(b[2])
    big = sorted(G, key=lambda o: -len(G[o]))
    print('Order %d: %d words, %d odd parts; best %d d=%d o=%d: o size rank %d, o group size %d (largest group o=%d with %d)'
          % (n, len(W), len(G), b[1], b[2], ob, os_.index(ob) + 1, len(G[ob]), big[0], len(G[big[0]])))
