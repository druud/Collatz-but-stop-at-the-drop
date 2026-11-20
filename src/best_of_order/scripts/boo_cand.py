# B120: certified candidates for the best of Order n from the best of Order n-1: insert one 1 (and one 0
# when p2(n) = p2(n-1) + 2) anywhere in its word; keep the admissible Order-n words; their best ratio is
# a certified start for boo.py (a word attains it). Compared with q(s0) (A122442) and the true best.
# theta = x*/c, the share of the gap (1 - q = (1 - 3^n/2^L)(1 - theta)). Integers and rationals only.
# Usage, from Lean/best_of_order (the smallest starts from data/b122442.txt, OEIS A122442): python3 scripts/boo_cand.py N0 N1
# (N1 <= 124; the bests from data/b402443_347.txt)
import sys
from fractions import Fraction as F
p2 = lambda m: (3 ** m).bit_length()
def T(x, L):
    for _ in range(L): x = (3 * x + 1) // 2 if x & 1 else x // 2
    return x
def word(c, L):
    w = []
    for _ in range(L): w.append(c & 1); c = (3 * c + 1) // 2 if c & 1 else c // 2
    return w
def cid(w, n):                                   # class id of an Order-n word, or None if not admissible
    r, a, b, j = 0, 1, 0, 0
    for l, e in enumerate(w):
        if l and 3 ** j < 2 ** l: return None    # dropped too early
        t = (e - b) % 2; v = a * t + b; r += t * 2 ** l
        if e: a, b, j = 3 * a, (3 * v + 1) // 2, j + 1
        else: b = v // 2
    if j != n or 3 ** j >= 2 ** len(w): return None
    return r if r > 1 else r + 2 ** len(w)
def theta(c, n):
    L = p2(n); return F(2 ** L * T(c, L) - 3 ** n * c, c * (2 ** L - 3 ** n))
A = {int(a): int(b) for a, b in (l.split() for l in open('data/b122442.txt'))}
ref = {int(a): int(b) for a, b in (l.split() for l in open('data/b402443_347.txt') if l.strip() and l[0] != '#') if 1 <= int(a) <= 124}
N0, N1 = int(sys.argv[1]), int(sys.argv[2]); win = [0, 0, 0]
for n in range(N0, N1 + 1):
    L, L1 = p2(n), p2(n - 1); w = word(ref[n - 1], L1); cs = set()
    for i in range(L1 + 1):
        u = w[:i] + [1] + w[i:]
        if L == L1 + 1: cs.add(cid(u, n))
        else:
            for k in range(len(u) + 1): cs.add(cid(u[:k] + [0] + u[k:], n))
    cs.discard(None)
    cb = max(cs, key=lambda c: F(T(c, L), c)) if cs else None
    ts0, tb = theta(A[n + 1], n), theta(ref[n], n); tc = theta(cb, n) if cb else F(0)
    win[0] += tc > ts0; win[1] += cb == ref[n]; win[2] += max(tc, ts0) > ts0
    print(n, 'cands', len(cs), 'theta s0/best', '%d/1000' % (1000 * ts0 / tb), 'cand/best', '%d/1000' % (1000 * tc / tb),
          'hit' if cb == ref[n] else '', flush=True)
print('cand beats s0:', win[0], 'cand = best:', win[1], 'of', N1 - N0 + 1)
