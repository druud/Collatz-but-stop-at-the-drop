# B120: both sides in turns. Cut after the w-th 1; G = A + B, A = rho_p (3^(n-w) + lam/3^w) (start side),
# B = rho_s - lam 2^m y/3^w (drop side), lam = lam*. A word can be the best only if A + max B >= 0 and
# B + max A >= 0 (maxima over the Order's words at that w). Per w: distinct prefixes / suffix values surviving,
# and words surviving both, out of all. Usage: mitm4.py n_from n_to
import sys
from fractions import Fraction as F
T = lambda x: (3*x+1)//2 if x & 1 else x//2
p2 = lambda m: (3**m).bit_length()
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    L = p2(n); W = []
    for r in range(3, 2**L, 2):
        x = r; q = 0; e = []
        for l in range(L):
            e.append(x & 1); q += x & 1; x = T(x)
            if 3**q < 2**(l+1): break
        if l == L-1 and q == n: W.append((F(x, r), r, e))
    W.sort(reverse=True); fb, cb, eb = W[0]; lam = fb * 2**L - 3**n
    out = []
    for w in range(1, n):
        R = []
        for f, c, e in W:
            m = [k for k in range(L) if e[k]][w-1] + 1
            rp = sum(3**(w-1-sum(e[:k])) * 2**k for k in range(m) if e[k])
            rs = 0; q = w
            for k in range(m, L):
                if e[k]: q += 1; rs += 3**(n-q) * 2**k
            y = c
            for _ in range(m): y = T(y)
            R.append((tuple(e[:m]), rp * (3**(n-w) + lam / 3**w), rs - lam * 2**m * F(y, 3**w)))
        mA = max(t[1] for t in R); mB = max(t[2] for t in R)
        pre = {t[0] for t in R}; preS = {t[0] for t in R if t[1] + mB >= 0}
        both = sum(1 for t in R if t[1] + mB >= 0 and t[2] + mA >= 0)
        out.append('%d:%d/%d,%d' % (w, len(preS), len(pre), both))
    print('Order %d (%d words) best %d  w:prefixes kept/all,words kept  %s' % (n, len(W), cb, ' '.join(out)))
