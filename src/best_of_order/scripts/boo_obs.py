# B138/B148: per Order n <= N, from the bests (b-file "n c") and the smallest starts (data/b122442.txt, s0 = a(n+1)):
# checks each best's word (Order n, first drop at L), its drop value d and window W = the largest x a class id
# with a higher ratio could have (Theorem B: x (2^L d - 3^n c) < R c), and theta(s0)/theta(best) = (rho0 c)/(rho c0).
# Writes the certificate file "n c d W". Integers and fractions only. Usage: boo_obs.py bests N certfile
import sys
from fractions import Fraction as F
p2 = lambda m: (3**m).bit_length()
B = {int(a): int(b) for a, b in (l.split() for l in open(sys.argv[1]) if l.strip() and not l.startswith('#'))}
A = {int(a): int(b) for a, b in (l.split() for l in open('data/b122442.txt'))}
N = int(sys.argv[2])
def drop(x, n, L):
    y = x; k = 0
    for l in range(L):
        if y & 1: y = (3*y + 1)//2; k += 1
        else: y //= 2
        if l + 1 < L: assert y >= x, (n, x, l)            # no drop before L (width identity range)
    assert k == n and y < x, (n, x)
    return y
eq = []; worst = (F(2), 0); W = {}
with open(sys.argv[3], 'w') as cf:
    cf.write('# n c d W: c the best of Order n, d = T^L(c), W = ceil(R(n) c / (2^L d - 3^n c)): a class id with a\n'
             '# higher ratio than c is below W (Theorem B). Recheck of one Order: boo_ties.cpp n n (exact, no tie, none better).\n')
    for n in range(1, N + 1):
        L = p2(n); c = B[n]; d = drop(c, n, L); s0 = A[n + 1]; d0 = drop(s0, n, L)
        R = sum(3**(n-q-1) * 2**(p2(q)-1) for q in range(n))
        g = 2**L * d - 3**n * c; w = -(-R * c // g); W[n] = w
        cf.write('%d %d %d %d\n' % (n, c, d, w))
        rho, rho0 = 2**L * d - 3**n * c, 2**L * d0 - 3**n * s0
        assert F(d, c) >= F(d0, s0)
        r = F(rho0 * c, rho * s0)
        if c == s0: eq.append(n)
        elif r < worst[0]: worst = (r, n)
print('Orders 1..%d: best = s0 at %d; others %s' % (N, len(eq), [n for n in range(1, N+1) if n not in eq]))
r, n = worst
print('min theta(s0)/theta(best) = %s at Order %d; > 41/100: %s; > 2/5: %s; > 1/3: %s' % (r, n, r > F(41,100), r > F(2,5), r > F(1,3)))
m = max(W, key=W.get); print('largest window W: Order %d, W = %d (bit length %d)' % (m, W[m], W[m].bit_length()))
