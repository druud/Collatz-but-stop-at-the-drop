#!/usr/bin/env python3
# The numbers of the paper "The best of the Order", recomputed and compared with the paper's text.
# Exact integers and fractions only. Every check prints OK, DIFF (computed against the paper) or SKIP.
# Run from Lean/best_of_order:
#   python3 scripts/paper_numbers.py [--seeds=FILE] [--appendix] [--beam]
# Without options: what the data files of data/ and a word list up to Order 16 can show (a few minutes).
# --seeds=FILE: another copy of the b-file of A122442 (a(n+1) = the smallest start of Order n) than
#   data/b122442.txt (the run to n = 400 that the searches used; https://oeis.org/A122442/b122442.txt).
# --appendix: also rerun the scripts of Appendix A and Remark "Both sides in turns" (mitm4.py, aim_cross.py,
#   aim_area.py, ideal_lines.py, mitm_search.py, boo.py; about 3 minutes) and compare their numbers.
# --beam: also rerun boo_beam.py 3 8 (long, one thread) and compare it with data/boo_beam_3_8.out; without
#   it the Orders of Appendix A are read from that saved output.
# The two slow checks are in C++ (paper_numbers_slow.cpp, about 2 minutes): Table 1 for Orders 17..21 and
#   the node counts of the best-first search for Orders 1..124.
# A few numbers have their own scripts and are not rerun here; the output ends with their list.
import sys, heapq, time, os, re, subprocess
from fractions import Fraction as F
from math import gcd
from collections import defaultdict

SEEDS, APPENDIX, BEAM = 'data/b122442.txt', False, False
for a in sys.argv[1:]:
    if a.startswith('--seeds='): SEEDS = a[8:]
    elif a == '--appendix': APPENDIX = True
    elif a == '--beam': BEAM = True
    else: sys.exit('usage: paper_numbers.py [--seeds=FILE] [--appendix] [--beam]')

p2 = lambda m: (3 ** m).bit_length()
T = lambda x: (3 * x + 1) // 2 if x & 1 else x // 2
def wall(n): return sum(3 ** (n - 1 - m) * 2 ** (p2(m) - 1) for m in range(n))

count = {'OK': 0, 'DIFF': 0, 'SKIP': 0}
def check(what, got, paper):
    s = 'OK' if got == paper else 'DIFF'; count[s] += 1
    print('%-4s %s: %s' % (s, what, got) + ('' if s == 'OK' else '   (paper: %s)' % (paper,)), flush=True)
def skip(what, why):
    count['SKIP'] += 1; print('SKIP %s: %s' % (what, why), flush=True)

def words(n):
    """All words of Order n >= 2 as (c, rho, d, word): depth-first over the prefixes with 3^j > 2^l."""
    L = p2(n); out = []; st = [(1, 1, 1, 2, 1, 1)]          # r, ones j, letters l, T^l(r), rho_j, word bits
    while st:
        r, j, l, b, rho, w = st.pop()
        if 3 ** j < 2 ** l:
            if j == n and l == L: out.append((r, rho, b, w))
            continue
        if j > n or l >= L: continue
        for t in (0, 1):
            v = 3 ** j * t + b; r2 = r + t * 2 ** l
            if v & 1: st.append((r2, j + 1, l + 1, (3 * v + 1) // 2, 3 * rho + 2 ** l, w | 1 << l))
            else: st.append((r2, j, l + 1, v // 2, rho, w))
    return out
def trajectory(n, c):
    """(d, rho) if c's first L steps are a word of Order n, else None."""
    L = p2(n); x = c; j = 0
    for l in range(L):
        j += x & 1; x = T(x)
        if l + 1 < L and 3 ** j < 2 ** (l + 1): return None
    return (x, 2 ** L * x - 3 ** n * c) if j == n and 3 ** n < 2 ** L else None

t00 = time.time()
cert = [tuple(map(int, l.split())) for l in open('data/best_cert_378.txt') if l.strip() and l[0] != '#']
bfile = {int(a): int(b) for a, b in (l.split() for l in open('data/b402443_378.txt') if l.strip() and l[0] != '#')}
BEST = {n: c for n, c, d, W in cert}
seed = None
if SEEDS:
    A = {int(a): int(b) for a, b in (l.split() for l in open(SEEDS) if l.strip() and l[0] != '#')}
    seed = {k - 1: v for k, v in A.items() if k >= 2}

print('--- The data files')
bad = 0
for n, c, d, W in cert:
    tr = trajectory(n, c)
    if tr is None or tr[0] != d or not d < c or W != -(-wall(n) * c // tr[1]) or bfile.get(n) != c: bad += 1
check('certificate rows (word of Order n, drop value, window, b-file) that fail, of %d' % len(cert), bad, 0)
check('Orders of the certificate file', (cert[0][0], cert[-1][0], len(cert)), (1, 378, 378))

print('--- Chapter 2: Order 6, the number of words, ties')
WL = {n: words(n) for n in range(2, 17)}
w6 = sorted(WL[6], key=lambda t: F(t[1], t[0]), reverse=True)
check('Order 6: number of words', len(w6), 12)
check('Order 6: the three highest rho/c as (c, rho)', [(c, r) for c, r, d, w in w6[:3]], [(347, 989), (287, 697), (507, 1085)])
check('Order 6: the best and its drop value', (w6[0][0], w6[0][2]), (347, 248))
check('Order 6: largest constant (c, rho)', max((r, c) for c, r, d, w in w6)[::-1], (507, 1085))
check('Order 6: smallest class id (c, rho)', min((c, r) for c, r, d, w in w6), (287, 697))
def nwords(n):
    L = p2(n); cur = {0: 1}
    for l in range(1, L + 1):
        nxt = defaultdict(int)
        for j, k in cur.items():
            for j2 in (j, j + 1):
                if j2 <= n and (3 ** j2 > 2 ** l or (l == L and j2 == n)): nxt[j2] += k
        cur = nxt
    return cur.get(n, 0)
check('number of words, Orders 1..10', [nwords(n) for n in range(1, 11)], [1, 1, 2, 3, 7, 12, 30, 85, 173, 476])
check('the DP count equals the word list, Orders 2..16', all(nwords(n) == len(WL[n]) for n in WL), True)
check('digits of the number of words, Orders 124 and 378', (len(str(nwords(124))), len(str(nwords(378)))), (53, 168))
groups = {}
for n in WL:
    g = defaultdict(list)
    for c, r, d, w in WL[n]: g[F(r, c)].append(c)
    groups[n] = [sorted(v) for v in g.values() if len(v) > 1]
first = min(n for n in groups if groups[n])
check('first Order with a tie, and its class ids', (first, groups[first]), (9, [[21223, 25691]]))
check('Order 13: largest set of class ids with one ratio', max(len(v) for v in groups[13]), 16)
check('Order 16: sets of equal ratios', len(groups[16]), 56)
tot = 0; kmax = (0, 0); tied = []
for n, c, d, W in cert:
    rb = trajectory(n, c)[1]; g = gcd(c, rb); u, v = c // g, rb // g
    K = min(W // u, wall(n) // v); tot += K; kmax = max(kmax, (K, n))
    for k in range(1, K + 1):
        x = k * u
        if x == c or x < 2: continue
        tr = trajectory(n, x)
        if tr is not None and tr[1] * c == rb * x: tied.append((n, x))
check('tie candidates of the bests, Orders 1..378', tot, 7582)
check('most tie candidates (number, Order)', kmax, (1063, 262))
check('ties of the best, Orders 1..378', tied, [])

print('--- Chapter 4: the ceiling')
bad = []
for n in range(1, 2001):
    L = p2(n); lo, hi = 0, 1
    while (3 * hi + 1) ** n >= 2 ** L * hi ** n: hi *= 2
    while hi - lo > 1:
        m = (lo + hi) // 2
        if (3 * m + 1) ** n < 2 ** L * m ** n: hi = m
        else: lo = m
    if not wall(n) < hi * (2 ** L - 3 ** n): bad.append(n)
check('Orders n <= 2000 with x*(wall) >= t_n', bad, [])

print("--- Chapter 5: Dinkelbach's steps")
def dinkel(ws, start):                                       # the class ids visited; an argmax tie: the smaller c
    by = {c: r for c, r, d, w in ws}; path = [start]
    while True:
        c0 = path[-1]; r0 = by[c0]
        c1 = max(by, key=lambda c: (by[c] * c0 - r0 * c, -c))
        if by[c1] * c0 - r0 * c1 == 0: return path
        path.append(c1)
s0 = {n: min(c for c, r, d, w in WL[n]) for n in WL}
wc = {n: max((r, c) for c, r, d, w in WL[n])[1] for n in WL}
check('Order 6: steps from the smallest start', dinkel(WL[6], 287), [287, 347])
check('Order 6: steps from the wall word', dinkel(WL[6], 507), [507, 347])
check('Order 13: number of words', len(WL[13]), 8045)
check('Order 13: steps from the wall word', dinkel(WL[13], wc[13]), [941051, 40699, 6427, 319, 159])
check('Order 13: steps from the smallest start', dinkel(WL[13], s0[13]), [159])
st_s = {n: len(dinkel(WL[n], s0[n])) - 1 for n in WL}; st_w = {n: len(dinkel(WL[n], wc[n])) - 1 for n in WL}
check('Orders 2..16: most steps from the smallest start, and the Orders with a step', (max(st_s.values()), [n for n in st_s if st_s[n]]), (1, [6, 8, 14]))
check('Orders 2..16: most steps from the wall word, and the Orders with that many', (max(st_w.values()), [n for n in st_w if st_w[n] == max(st_w.values())]), (4, [13, 16]))
check('Orders 2..16: the word list gives the best of the certificate file', all(dinkel(WL[n], s0[n])[-1] == BEST[n] for n in WL), True)

print('--- Chapter 6: seeds and cost')
cur = {0: 1}
for l in range(1, 29):
    nxt = defaultdict(int)
    for j, k in cur.items():
        for j2 in (j, j + 1):
            if 3 ** j2 > 2 ** l: nxt[j2] += k
    cur = nxt
check('residues left by the wheel modulo 2^28', sum(cur.values()), 3524586)
Wn = {n: W for n, c, d, W in cert}
check('largest window of Orders 1..124 is below 2^26', max(Wn[n] for n in range(1, 125)) < 2 ** 26, True)
check('R(n)/(3^n - 2^n) below 31 at Order 124, below 92 at Order 378', (wall(124) < 31 * (3 ** 124 - 2 ** 124), wall(378) < 92 * (3 ** 378 - 2 ** 378)), (True, True))
check('R(n) <= n 3^(n-1) and rho >= 3^n - 2^n on the word list', all(wall(n) <= n * 3 ** (n - 1) and min(r for c, r, d, w in WL[n]) == 3 ** n - 2 ** n for n in WL), True)
check('largest window of Orders 1..378 (Order, W)', max((Wn[n], n) for n in Wn)[::-1], (378, 886522563681567))
if seed:
    check('the smallest starts of the word list (Orders 2..16) are the seeds', all(seed[n] == s0[n] for n in WL), True)
    eq = [n for n in BEST if seed[n] == BEST[n]]
    check('Orders 1..124 with the smallest start as the best', sum(1 for n in eq if n <= 124), 98)
    check('Orders 1..378 with the smallest start as the best', len(eq), 307)
    wmax = 0
    for n in range(379, 400):
        d, rho = trajectory(n, seed[n]); wmax = max(wmax, -(-wall(n) * seed[n] // rho))
    check('largest window of the seeds, Orders 379..399', wmax, 17216187145311549)
    check('s0 <= best <= s0 R(n)/(3^n - 2^n) for all Orders 1..378', all(seed[n] <= BEST[n] and BEST[n] * (3 ** n - 2 ** n) <= wall(n) * seed[n] for n in BEST), True)
    check('best < n s0/2 for Orders 3..378', all(2 * BEST[n] < n * seed[n] for n in BEST if n >= 3), True)
    m = max((F(BEST[n], seed[n]), n) for n in BEST)
    check('largest best/s0 (value, Order), between 3 and 16/5', (str(m[0]), m[1], 3 < m[0] < F(16, 5)), ('1097165/347477', 107, True))
    print('--- Chapter 7: the smallest start')
    th = []
    for n in BEST:
        if seed[n] != BEST[n]:
            th.append((F(trajectory(n, seed[n])[1] * BEST[n], trajectory(n, BEST[n])[1] * seed[n]), n))
    th.sort()
    check('theta(s0)/theta(best) > 1/4 for all Orders 1..378', th[0][0] > F(1, 4), True)
    check('the five Orders with the smallest theta(s0)/theta(best)', [n for r, n in th[:5]], [272, 361, 363, 256, 91])
    check('the smallest lies between 25/100 and 26/100', F(25, 100) < th[0][0] < F(26, 100), True)
else:
    skip('seeds as bests (98, 285), windows of Orders 348..399, theta(s0)/theta(best)', 'needs the b-file of A122442')

print('--- Chapter 7: backward ranking (Table 1)')
K0 = dict(zip(range(2, 26), [1, 1, 3, 2, 6, 4, 8, 7, 9, 9, 12, 13, 19, 14, 16, 16, 18, 24, 21, 23, 25, 24, 29, 29]))
def k0(n, ws):
    L = p2(n); cb, rb = max(((c, r) for c, r, d, w in ws), key=lambda t: (F(t[1], t[0]), -t[0]))
    def sums(c, w):                                          # c_best * S_k for k = 1..L
        ones = bin(w).count('1'); s = 0; out = []
        for l in range(L - 1, -1, -1):                       # ones = w_l, the ones up to and including letter l
            e = w >> l & 1
            s += 2 ** l * (e * 3 ** (n - ones) * cb - rb * (c >> l & 1))
            ones -= e; out.append(s)
        return out
    wb = next(w for c, r, d, w in ws if c == cb); sb = sums(cb, wb)
    last = 0                                                 # the largest k at which the best is not the strict maximum
    for c, r, d, w in ws:
        if c == cb: continue
        so = sums(c, w)
        for k in range(L, last, -1):
            if so[k - 1] >= sb[k - 1]: last = k; break
    return last + 1
got = {n: k0(n, WL[n]) for n in WL}
top = 16
skip('Table 1, Orders 17..21', 'in paper_numbers_slow.cpp (22..25: its --k0=25)')
check('Table 1: k0 for Orders 2..%d' % top, [got[n] for n in range(2, top + 1)], [K0[n] for n in range(2, top + 1)])
check('Table 1: L for Orders 2..25', [p2(n) for n in range(2, 26)], [4, 5, 7, 8, 10, 12, 13, 15, 16, 18, 20, 21, 23, 24, 26, 27, 29, 31, 32, 34, 35, 37, 39, 40])
check('Table 1 as printed: L/2 < k0 < 4L/5 for Orders 15..25', all(p2(n) < 2 * K0[n] and 5 * K0[n] < 4 * p2(n) for n in range(15, 26)), True)
check('Order 14: k0 and L', (got[14], p2(14)), (19, 23))

print('--- Chapter 7: merging trajectories')
odd = lambda x: x >> ((x & -x).bit_length() - 1)
G = defaultdict(list)
for n, c, d, W in cert: G[odd(d)].append(n)
by = defaultdict(list)
for o, ns in G.items(): by[len(ns)].append(o)
check('odd parts of the drop values, Orders 1..378', len(G), 240)
check('odd parts shared by 10, 9 and 5 Orders', (by[10], by[9], sorted(by[5])), ([61], [12729682859], [619739, 92485801, 1064232949, 30643528277]))
check('number of odd parts shared by 4, 3, 2 Orders and by one', (len(by[4]), len(by[3]), len(by[2]), len(by[1])), (8, 18, 45, 163))
check('no odd part is shared by more Orders', sorted(by), [1, 2, 3, 4, 5, 9, 10])
x = 27; tr27 = []
while x != 1: tr27.append(x); x = T(x)
tr27.append(1)
on = [o for o in tr27 if o in G]
check('odd parts on the trajectory of 27, in its order', on, [31, 167, 325, 61, 23, 5, 1])
check('Orders whose drop value has such an odd part', sum(len(G[o]) for o in on), 21)

print('--- Appendix A: the inverse tree of 91')
TOP = 2 ** 22; reach = bytearray(TOP)                        # reach[x] = 1: the trajectory of x meets 91
for x in range(2, TOP):
    y = x; hit = 0
    while True:
        if y == 91: hit = 1; break
        if y < x: hit = reach[y]; break
        if y == 1 or (y == 2 and x == 2): break
        y = T(y)
    reach[x] = hit
inr = [c for c in {BEST[n] for n in range(1, 125)} if 91 < c < TOP]
nodd = (TOP - 92) // 2; hodd = sum(reach[x] for x in range(93, TOP, 2))
check('bests of Orders 1..124 in (91, 2^22), and those in the inverse tree of 91', (len(inr), sum(reach[c] for c in inr)), (106, 21))
check('per cent (rounded) of the bests, and of the odd starts there, in that tree', ((200 * sum(reach[c] for c in inr) + len(inr)) // (2 * len(inr)), (200 * hodd + nodd) // (2 * nodd)), (20, 28))

print('--- Chapter 6: the cost of the best-first search')
def boo(n):                                                  # as boo.py: (best, nodes)
    L = p2(n); tail = [0] * (n + 2)
    for o in range(n, 0, -1): tail[o - 1] = tail[o] + 3 ** (n - o) * 2 ** (p2(o - 1) - 1)
    c = seed[n]; d = c
    for _ in range(L): d = T(d)
    bn, bd = d, c; best = c; seen = 0; h = [(1, 1, 1, 2, 1)]
    while h:
        r, j, l, b, rho = heapq.heappop(h); seen += 1
        g = 2 ** L * bn - 3 ** n * bd
        if r * g >= tail[0] * bd: break
        if 3 ** j < 2 ** l:
            if j == n and l == L:
                c = r if r > 1 else r + 2 ** L; d = c
                for _ in range(L): d = T(d)
                if d * bd > bn * c: bn, bd, best = d, c, c
            continue
        if j > n or n - j > L - 1 - l: continue
        if r * g >= (3 ** (n - j) * rho + tail[j]) * bd: continue
        for t in (0, 1):
            v = 3 ** j * t + b; r2 = r + t * 2 ** l
            if v & 1: heapq.heappush(h, (r2, j + 1, l + 1, (3 * v + 1) // 2, 3 * rho + 2 ** l))
            else: heapq.heappush(h, (r2, j, l + 1, v // 2, rho))
    return best, seen
if seed:
    b, s = zip(*(boo(n) for n in range(1, 61)))
    check('best-first search, Orders 1..60: the bests of the certificate file', list(b), [BEST[n] for n in range(1, 61)])
    skip('node counts of the best-first search, Orders 1..124', 'in paper_numbers_slow.cpp')
else:
    skip('the best-first search and its node counts', 'needs the b-file of A122442; the counts are in paper_numbers_slow.cpp')

print('--- Appendix A and Remark "Both sides in turns": their own scripts')
def run(*args):
    """Output of scripts/<args[0]> run from Lean/best_of_order with this Python."""
    r = subprocess.run([sys.executable, os.path.join('scripts', args[0])] + list(args[1:]), capture_output=True, text=True)
    if r.returncode: sys.exit('%s failed:\n%s' % (' '.join(args), r.stderr))
    return r.stdout
def span(v): return (min(v), max(v))
if APPENDIX:
    out = run('mitm4.py', '4', '13')
    check('words passing both tests at each cut, Orders 4..13 (mitm4.py): fewest, most',
          span([int(k) for k in re.findall(r' \d+:\d+/\d+,(\d+)', out)]), (1, 3))
    out = run('aim_cross.py', '4', '14')
    check("the best's crossings with the aim, Orders 4..14 (aim_cross.py): fewest, most",
          span([int(k) for k in re.findall(r'crossings best (\d+)', out)]), (2, 8))
    out = run('aim_area.py', '5', '13')
    check('the rank of the best by the area, Orders 5..13 (aim_area.py): lowest, highest',
          span([int(k) for k in re.findall(r'area rank (\d+)', out)]), (3, 1337))
    out = run('ideal_lines.py', '5', '13')
    check('the rank of the best by the diagonal, Orders 5..13 (ideal_lines.py): lowest, highest',
          span([int(k) for k in re.findall(r'diag rank (\d+)', out)]), (2, 6425))
    if seed:
        out = run('mitm_search.py', '22', '22', '0', 'x', 'seedc')
        check('the backward search primed with s0, Order 22 (mitm_search.py): best, nodes',
              re.findall(r'best (\d+) ok .* nodes (\d+)', out), [('871', '96743')])
        out = run('boo.py', '22', '22')
        check('the best-first search, Order 22 (boo.py): best, nodes', out.split()[:4], ['22', '871', 'nodes', '1505'])
    else: skip('mitm_search.py, boo.py at Order 22', 'need the b-file of A122442')
else:
    skip('mitm4.py, aim_cross.py, aim_area.py, ideal_lines.py, mitm_search.py, boo.py', 'add --appendix (about 3 minutes)')
saved = open('data/boo_beam_3_8.out').read()
if BEAM:
    out = run('boo_beam.py', '3', '8')
    check('boo_beam.py 3 8 against data/boo_beam_3_8.out (lines that differ)',
          sum(a != b for a, b in zip(out.splitlines(), saved.splitlines())) + abs(len(out.splitlines()) - len(saved.splitlines())), 0)
else: out = saved
check('candidates from earlier Orders that beat s0 (boo_beam.py 3 8%s): Orders' % ('' if BEAM else ', saved output'),
      [int(l.split()[0]) for l in out.splitlines() if '=best' in l], [6, 8, 107])
if seed:
    check('... the run covers exactly the Orders 3..124 whose best is not s0', [int(l.split()[0]) for l in out.splitlines()],
          [n for n in range(3, 125) if seed[n] != BEST[n]])

print('--- Checked elsewhere')
for t in ('Remark "Seeds", Appendix A: a guessed first ratio costs about twice the nodes: paper_numbers_slow.cpp',
          'Chapter 6: that the scan found no better class id: boo_scan.cpp, boo_ties.cpp (the runs themselves)'):
    print('     ' + t)
print('--- %d OK, %d DIFF, %d SKIP (%.0f s)' % (count['OK'], count['DIFF'], count['SKIP'], time.time() - t00))
sys.exit(1 if count['DIFF'] else 0)
