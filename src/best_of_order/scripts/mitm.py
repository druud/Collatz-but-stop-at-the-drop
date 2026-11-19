# B120: Dinkelbach from both ends, meeting at letter m. With w ones in the first m letters, prefix rho_p,
# middle value y = T^m(c) = (3^w c + rho_p)/2^m, and the suffix (the word of y, L - m letters, n - w ones) rho_s
# (its ones counted on: rho = 3^(n-w) rho_p + rho_s), c = (2^m y - rho_p)/3^w, so
#   G = rho - lam c = rho_p (3^(n-w) + lam/3^w)  +  (rho_s - lam 2^m y/3^w),
# a prefix part and a suffix part; the only tie is y = b_p (mod 3^w), b_p = T^m of the prefix class r_p.
# Checks the split exactly and ranks the best's two parts among the prefixes (same w) and middle values (same w).
import sys
from fractions import Fraction as F
T = lambda x: (3*x+1)//2 if x & 1 else x//2
p2 = lambda m: (3**m).bit_length()
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    L = p2(n); m = L // 2; W = []
    for r in range(3, 2**L, 2):
        x = r; q = 0; e = []
        for l in range(L):
            e.append(x & 1); q += x & 1; x = T(x)
            if 3**q < 2**(l+1): break
        if l == L-1 and q == n: W.append((F(x, r), r, e))
    W.sort(reverse=True); lam = None
    rows = []
    for f, c, e in W:
        w = sum(e[:m]); rp = sum(3**(w-1-sum(e[:k])) * 2**k for k in range(m) if e[k])   # prefix rho
        rs = 0; q = w
        for k in range(m, L):
            if e[k]: q += 1; rs += 3**(n-q) * 2**k
        y = c
        for _ in range(m): y = T(y)
        assert (3**w * c + rp) == 2**m * y and 3**(n-w) * rp + rs == f * c * 2**L - 3**n * c
        rows.append((c, w, rp, rs, y))
    c0, w0, rp0, rs0, y0 = rows[0]; lam = F(3**(n-w0) * rp0 + rs0, c0)
    A = lambda t: t[2] * (3**(n-t[1]) + lam / 3**t[1])
    Bs = lambda t: t[3] - lam * 2**m * F(t[4], 3**t[1])
    for t in rows: assert A(t) + Bs(t) == 3**(n-t[1]) * t[2] + t[3] - lam * t[0]
    same = [t for t in rows if t[1] == w0]
    ra = sorted({A(t) for t in same}, reverse=True).index(A(rows[0])) + 1
    rb = sorted({Bs(t) for t in same}, reverse=True).index(Bs(rows[0])) + 1
    print('Order %d L %d m %d: best %d, w %d (%d words with that w); prefix part rank %d of %d prefixes, suffix part rank %d'
          % (n, L, m, c0, w0, len(same), ra, len({t[2] for t in same}), rb))
