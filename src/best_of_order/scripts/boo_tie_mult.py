# B152+: ties of the best by divisibility, exact. T^L(c)/c = 3^n/2^L + rho/(2^L c), so c ties c* iff
# rho c* = rho* c. With g = gcd(c*, rho*), u = c*/g, v = rho*/g: c = k u and rho = k v for an integer k >= 1.
# A tie or better lies below the window W (Theorem 6.1, c <= W), so k <= W/u; also rho <= R(n), so k <= R/v.
# Each candidate c = k u (k != 1) is checked by its trajectory: an Order-n word (drop exactly at L) and
# rho c* = rho* c. A candidate that is not a class id cannot tie (its class id would beat c*).
# Usage: boo_tie_mult.py certfile [n1 n2]   (certfile lines "n c d W"); or: boo_tie_mult.py --pair n c
import sys
p2 = lambda m: (3**m).bit_length()
def word(n, c):
    L = p2(n); x = c; j = 0
    for l in range(L):
        if x & 1: x = (3*x + 1) >> 1; j += 1
        else: x >>= 1
        if l + 1 < L and 3**j < 2**(l + 1): return None
    return (2**L * x - 3**n * c) if j == n and 3**n < 2**L else None
def R(n): return sum(3**(n-1-m) * 2**(p2(m)-1) for m in range(n))
def ties(n, cb, W):
    rb = word(n, cb); assert rb is not None, (n, cb)
    from math import gcd
    g = gcd(cb, rb); u, v = cb // g, rb // g
    K = min(W // u, R(n) // v); out = []
    for k in range(1, K + 1):
        c = k * u
        if c == cb or c < 2: continue
        r = word(n, c)
        if r is not None and r * cb == rb * c: out.append(c)
    return K, out
if sys.argv[1] == '--pair':
    n, c = int(sys.argv[2]), int(sys.argv[3]); print(ties(n, c, 2**(p2(n)+1)))
else:
    rows = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and l[0] != '#']
    n1, n2 = (int(sys.argv[2]), int(sys.argv[3])) if len(sys.argv) > 3 else (1, 10**9)
    tot = 0; found = 0; kmax = (0, 0)
    for n, c, d, W in rows:
        if not n1 <= n <= n2: continue
        K, t = ties(n, c, W); tot += K; kmax = max(kmax, (K, n))
        if t: found += 1; print('Order', n, 'best', c, 'TIE', *t)
    print('Orders %d..%d: %d candidates in all, most %d at Order %d; Orders with a tie: %d' % (max(n1, rows[0][0]), min(n2, rows[-1][0]), tot, kmax[0], kmax[1], found))
