# The aim: the wall word started at its cycle point x* = R/(2^L - 3^n) (returns to x*: total ratio 1).
# Per word: the sign of T^l(c)/c - A_l, A_l = T_wall^l(x*)/x*, at l = 1..L (exact), the crossings,
# and how the best compares. Usage: python3 aim_cross.py n_from n_to
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
            sg = ''.join('+' if F(xs[l], r) > A[l] else '-' if F(xs[l], r) < A[l] else '0' for l in range(1, L+1))
            cr = sum(1 for a, b in zip(sg, sg[1:]) if a != b)
            rows.append((F(x, r), r, sg, cr))
    rows.sort(reverse=True)
    mx = max(t[3] for t in rows)
    from collections import Counter
    print('Order %d (%d words): crossings best %d, smallest %d, max %d; crossings of all: %s' % (n, len(rows), rows[0][3],
          min(rows, key=lambda t: t[1])[3], mx, sorted(Counter(t[3] for t in rows).items())))
    for f, r, sg, cr in rows[:3]: print('   %6d %s %d' % (r, sg, cr))
    s = min(rows, key=lambda t: t[1])
    if s is not rows[0]: print('   %6d %s %d (smallest)' % (s[1], s[2], s[3]))
