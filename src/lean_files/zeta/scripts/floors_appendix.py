# The floors appendix of the zeta paper (C167, 26 Nov 2026), in exact integers only.
# Run from Lean/accelerated_collatz/zeta:  python3 scripts/floors_appendix.py [N] [R]
#   Table 1: the floors theta_n = 3^n/2^p2(n) of the Orders 0..N (default 45) in their order on the
#            octave, with N(n) (A100982), the record marks, and the end ratio to the next floor up.
#   Table 2: the upper and lower record Orders up to R (default 20000), with p2.
# Floors are compared exactly: theta_a < theta_b  iff  3^a 2^p2(b) < 3^b 2^p2(a).
import sys
from functools import cmp_to_key

N = int(sys.argv[1]) if len(sys.argv) > 1 else 45
R = int(sys.argv[2]) if len(sys.argv) > 2 else 20000

def p2(n): return (3 ** n).bit_length()

def counts(N):                       # N(n) for n = 0..N, by the alive prefixes (paper 3, Ch. 3)
    out = [1, 1]                     # the word 0, and 10
    alive = {(1, 1): 1}              # (ones, letters) -> number of alive prefixes ending in a one
    for n in range(2, N + 1):
        # extend each alive prefix with n-1 ones by zeros while alive, then by the n-th one
        new = {}
        for (j, l), k in alive.items():
            while True:
                new[(j + 1, l + 1)] = new.get((j + 1, l + 1), 0) + k
                if 3 ** j > 2 ** (l + 1): l += 1
                else: break
        alive = new
        out.append(sum(alive.values()))
    return out

def cmp(a, b):
    x, y = 3 ** a * 2 ** p2(b), 3 ** b * 2 ** p2(a)
    return (x > y) - (x < y)

C = counts(N)
assert C[:11] == [1, 1, 1, 2, 3, 7, 12, 30, 85, 173, 476], C[:11]

up, low = [1], []                    # record Orders: highest floor so far (from 1), lowest (from 2,
hi = lo = 1                          # against theta_1; Order 1 is an upper record only)
for n in range(2, R + 1):
    if cmp(n, hi) > 0: up.append(n); hi = n
    if cmp(n, lo) < 0: low.append(n); lo = n

order = sorted(range(N + 1), key=cmp_to_key(cmp))   # theta_0 = 1/2 lowest
mark = lambda n: 'U' if n in up else ('L' if n in low else '')
print('Table 1: the floors of Orders 0..%d, lowest first' % N)
ratios = set()
for i, n in enumerate(order):
    m = order[i + 1] if i + 1 < len(order) else None      # the next floor up; after the top: 2 theta_0 = 1
    if m is None: r = '2^%d/3^%d' % (p2(n), n); key = ('2/3', n, p2(n))
    elif m > n: r = '3^%d/2^%d' % (m - n, p2(m) - p2(n)); key = ('3/2', m - n, p2(m) - p2(n))
    else: r = '2^%d/3^%d' % (p2(n) - p2(m), n - m); key = ('2/3', n - m, p2(n) - p2(m))
    ratios.add(key)
    print('%3d %3d %3d %22d %2s  %s' % (i + 1, n, p2(n), C[n], mark(n), r))
print('end ratios: %d distinct' % len(ratios), sorted(ratios))
print('Table 2: record Orders up to %d' % R)
print('upper:', len(up), up)
print('lower:', len(low), low)
print('p2 upper:', [p2(n) for n in up])
print('p2 lower:', [p2(n) for n in low])
print('record fractions, upper p2(n)/n:', ' '.join('%d/%d' % (p2(n), n) for n in up))
print('record fractions, lower (p2(n)-1)/n:', ' '.join('%d/%d' % (p2(n) - 1, n) for n in low))
print('DONE')
