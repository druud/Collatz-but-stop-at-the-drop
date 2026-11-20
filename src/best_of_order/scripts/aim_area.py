# Per word, the product over l = 1..L of (T^l(c)/c) / A_l (A the aim from x*, ends at 1): a log-area
# between the word and the aim, exact. Rank of the best by this area, and the word with the largest one.
import sys
from fractions import Fraction as F
T = lambda x: (3*x+1)//2 if x & 1 else x//2
p2 = lambda m: (3**m).bit_length()
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    L = p2(n); wall = [p2(q-1)-1 for q in range(1, n+1)]
    R = sum(3**(n-q-1) * 2**k for q, k in enumerate(wall))
    A = [F(R, 2**L - 3**n)]
    for k in range(L): A.append((3*A[-1]+1)/2 if k in wall else A[-1]/2)
    A = [a/A[0] for a in A]
    rows = []
    for r in range(3, 2**L, 2):
        x = r; q = 0; xs = [r]
        for l in range(L):
            q += x & 1; x = T(x); xs.append(x)
            if 3**q < 2**(l+1): break
        if l == L-1 and q == n:
            P = F(1)
            for l in range(1, L+1): P *= F(xs[l], r) / A[l]
            rows.append((F(x, r), r, P))
    best = max(rows); byP = sorted(rows, key=lambda t: -t[2])
    print(n, len(rows), 'best', best[1], 'area rank', [t[1] for t in byP].index(best[1]) + 1, 'top area', [t[1] for t in byP[:3]])
