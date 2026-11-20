# B120: certified candidates from the best of Order n-K, K = 1..KMAX: insert one 1 (plus one 0 when p2 grows
# by 2) per Order step, keeping the top M words by ratio at each step (a beam). Run on the Orders whose best
# is not s0 (A122442 a(n+1)): does any K give a word beating s0? Integers and rationals only.
# Usage, from Lean/best_of_order with b122442.txt (OEIS A122442) there: python3 scripts/boo_beam.py KMAX M
# (the bests of Orders 1..124 from data/b402443_347.txt; the run for KMAX = 3, M = 8: data/boo_beam_3_8.out)
import sys
from fractions import Fraction as F
import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'boo_cand.py')).read().split('A = {')[0])             # p2, T, word, cid, theta
A = {int(a): int(b) for a, b in (l.split() for l in open('b122442.txt'))}
ref = {int(a): int(b) for a, b in (l.split() for l in open('data/b402443_347.txt') if l.strip() and l[0] != '#') if 1 <= int(a) <= 124}
def step(cs, n):                                               # Order n-1 class ids -> Order n class ids
    L, L1 = p2(n), p2(n - 1); out = set()
    for c in cs:
        w = word(c, L1)
        for i in range(L1 + 1):
            u = w[:i] + [1] + w[i:]
            if L == L1 + 1: out.add(cid(u, n))
            else:
                for k in range(len(u) + 1): out.add(cid(u[:k] + [0] + u[k:], n))
    out.discard(None); return out
KMAX, M = int(sys.argv[1]), int(sys.argv[2])
for n in [n for n in sorted(ref) if n >= 3 and A[n + 1] != ref[n]]:
    L = p2(n); q = lambda c, m: F(T(c, p2(m)), c); res = []
    for K in range(1, KMAX + 1):
        if n - K < 1: break
        cs = {ref[n - K]}
        for m in range(n - K + 1, n + 1): cs = set(sorted(step(cs, m), key=lambda c: -q(c, m))[:M])
        cb = max(cs, key=lambda c: q(c, n))
        res.append('K%d %s%s' % (K, '%d/1000' % (1000 * theta(cb, n) / theta(ref[n], n)), '=best' if cb == ref[n] else ''))
    print(n, 's0', '%d/1000' % (1000 * theta(A[n + 1], n) / theta(ref[n], n)), ' '.join(res), flush=True)
