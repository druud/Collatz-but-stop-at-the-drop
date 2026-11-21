# B120: the best of Order n by meeting in the middle, cut after the w-th 1 (w = n//2 by default).
# lam0 = rho/c of the smallest start s (data/b122442.txt: A122442, a(n+1)); a word beats s only if
# G = rho - lam0 c >= 0, G = A + B: A = rho_p (3^(n-w) + lam0/3^w) (start side), B = rho_s - lam0 2^m y/3^w.
# Start side: the admissible prefixes ending in their w-th 1 (the Order-w words), per length m: max A, and
#   (r, b, rho_p) with T^m(2^m h + r) = 3^w h + b.
# Drop side: suffixes grown backward from the last letter (0) on classes z mod 2^k, the ruler checked from the
#   end (3^(n - ones after) > 2^position), rho_s from the end (the j-th 1 from the end counts 3^(j-1) 2^pos);
#   at a cut (n - w ones, letter m-1 a 1), the middle value y >= z, so B <= rho_s - lam0 2^m z/3^w; kept if
#   that + maxA[m] >= 0. Kept suffixes are joined with the prefixes of the same m by CRT (y = z mod 2^k,
#   y = b mod 3^w, b <= y < b + 3^w 2^k), c = r + 2^m (y - b)/3^w, exact. Integers and rationals only.
# Usage, from Lean/best_of_order (the smallest starts from data/b122442.txt, OEIS A122442): python3 scripts/mitm_search.py n_from n_to [w]
# (Appendix A, the backward search primed with the smallest start: mitm_search.py 22 22 0 x seedc: nodes 96743)
import sys, time
from fractions import Fraction as F
p2 = lambda m: (3**m).bit_length()
A122 = {int(a): int(b) for a, b in (l.split() for l in open('data/b122442.txt'))}
def run(n, w):
    L = p2(n); s0 = A122[n+1]; x = s0
    for _ in range(L): x = (3*x+1)//2 if x & 1 else x//2
    lam = F(2**L * x - 3**n * s0, s0)                        # rho/c of the smallest start
    R = sum(3**(n-q) * 2**(p2(q-1)-1) for q in range(1, n+1))     # the wall's rho, the largest
    CW = R * s0 // (2**L * x - 3**n * s0)                    # c > CW cannot beat s0 (2^L lam0 c > R)
    # start side
    pre = {}; st = [(1, 1, 1, 2, 1)] if w else []                         # (j ones, l letters, r, b, rho_p): word '1'
    while st:
        j, l, r, b, rho = st.pop()
        if j == w:
            pre.setdefault(l, []).append((r, b, rho))
            continue
        for e in (0, 1):
            t = (e - b) % 2; v = 3**j * t + b; r2 = r + t * 2**l
            k = (j, l+1, r2, v//2, rho) if e == 0 else (j+1, l+1, r2, (3*v+1)//2, 3*rho + 2**l)
            if 3**k[0] > 2**(l+1): st.append(k)
    if w == 0: pre = {}
    for v in pre.values(): v.sort(key=lambda t: -t[2])
    Aw = 3**(n-w) + lam / 3**w
    maxA = {m: max(rho for _, _, rho in v) * Aw for m, v in pre.items()}
    # bound for any state of the drop side: with j = n - s ones before letter p, the start part is at most
    # rho_max(p, j) (3^(n-j) + lam0/3^j), rho_max over the admissible prefixes of length p with j ones (DP)
    NEG = None; rmax = [[NEG] * (n + 1) for _ in range(L + 1)]; rmax[0][0] = 0
    for l in range(1, L + 1):
        for j in range(0, n + 1):
            if l < L and not 3**j > 2**l: continue
            a = rmax[l-1][j]; b2 = rmax[l-1][j-1] if j else NEG
            cands = [v for v in (a, 3*b2 + 2**(l-1) if b2 is not None else None) if v is not None]
            rmax[l][j] = max(cands) if cands else NEG
    PR = 0; POPS[0] = 0
    # drop side
    cuts = kept = pairs = 0; best = (F(x, s0), s0)
    st = [(1, 0, 0, 0)]                                      # (k letters, ones, z mod 2^k, rho_s): last letter 0
    while st:
        k, s, z, rho = st.pop(); POPS[0] += 1
        p = L - k                                            # the suffix starts at letter p
        j = n - s
        if PRUNE:
            if rmax[p][j] is None: continue
            zz = z
            if SEEDC:                                        # every start is >= s0: value at p >= 3^j s0/2^p
                lo = -((-3**j * s0) // 2**p); M = 2**k
                if zz < lo: zz += (lo - zz + M - 1) // M * M
                if WIN and zz * 2**p > 3**j * CW + rmax[p][j]: PR += 1; continue   # beyond the window c <= CW
            if rho - lam * 2**p * F(zz, 3**j) + rmax[p][j] * (3**(n-j) + lam / 3**j) < 0: PR += 1; continue
        if w == 0 and p == 0:                                # pure backward search: z is the class id
            c = z if z > 1 else z + 2**L; pairs += 1
            q = F(3**n * c + rho, 2**L * c)
            if q > best[0]: best = (q, c)
            continue
        if w and s == n - w and p in maxA:                   # a cut at m = p
            cuts += 1
            if rho - lam * 2**p * F(z, 3**w) + maxA[p] >= 0:
                kept += 1; M2, M3 = 2**k, 3**w
                Bub = rho - lam * 2**p * F(z, 3**w)
                for r, b, rp in pre[p]:                      # sorted by rho_p, largest first
                    if rp * Aw + Bub < 0: break
                    y = (z + M2 * ((b - z) * pow(M2, -1, M3) % M3)) % (M2 * M3)
                    if y < b: y += M2 * M3
                    c = r + 2**p * (y - b) // M3
                    if c < 3: continue
                    pairs += 1
                    q = F(3**n * c + 3**(n-w) * rp + rho, 2**L * c)
                    if q > best[0]: best = (q, c)
        if p == 0: continue
        for e in (0, 1):                                     # the letter at p-1
            s2 = s + e
            if s2 > n - w: continue
            if p - 1 >= 1 and not 3**(n - s2) > 2**(p-1): continue
            M = 2**(k+1)
            z2 = (2*z) % M if e == 0 else (2*z - 1) * pow(3, -1, M) % M
            st.append((k+1, s2, z2, rho + (3**s * 2**(p-1) if e else 0)))
    return best, sum(len(v) for v in pre.values()), cuts, kept, pairs, PR
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
POPS = [0]
SEEDC = 'seedc' in sys.argv
WIN = 'win' in sys.argv
PRUNE = len(sys.argv) <= 4 or sys.argv[4] != 'noprune'
ref = {int(a): int(b) for a, b in (l.split() for l in open('data/b402443_378.txt') if l.strip() and l[0] != '#')}
for n in range(N0, N1 + 1):
    t0 = time.time(); w = int(sys.argv[3]) if len(sys.argv) > 3 else n // 2
    (q, c), np_, cu, ke, pa, pr = run(n, w)
    print('Order %d w %d: best %d %s | prefixes %d, suffix cuts %d, kept %d, pairs %d, pruned %d, nodes %d, %.1fs'
          % (n, w, c, 'ok' if ref.get(n) == c else 'WRONG (ref %s)' % ref.get(n), np_, cu, ke, pa, pr, POPS[0], time.time() - t0), flush=True)
