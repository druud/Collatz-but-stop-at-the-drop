# Best of the Order (largest T^L(c)/c, c > 1) by best-first search on r, seeded with the smallest start
# value s (A122442, a(n+1), from data/b122442.txt). For an Order-n word with constant rho (2^L T^L(c) = 3^n c + rho)
# the ratio is 3^n/2^L + rho/(2^L c), so it beats the ratio q only if c < rho/(2^L q - 3^n); per node
# rho <= rho_hi = 3^(n-j) rho_j + tail_j (walls) and c >= r. Nodes are popped by r; the search stops at the
# first r beyond the global window rho_hi(root)/(2^L q - 3^n). Integers only. Usage: python3 boo.py N0 N1
import sys, heapq, time
p2 = lambda m: (3 ** m).bit_length()
A = {int(a): int(b) for a, b in (l.split() for l in open('data/b122442.txt'))}
def T(x, L):
    for _ in range(L): x = (3 * x + 1) // 2 if x & 1 else x // 2
    return x
def boo(n):
    L = p2(n); tail = [0] * (n + 2)
    for o in range(n, 0, -1): tail[o - 1] = tail[o] + 3 ** (n - o) * 2 ** (p2(o - 1) - 1)
    c = A[n + 1]; d = T(c, L); bn, bd = d, c                    # best ratio bn/bd; gap g/bd = 2^L q - 3^n
    best = c; seen = 0
    h = [(1, 1, 1, 2, 1)]                                         # (r, j, l, b, rho_j)
    while h:
        r, j, l, b, rho = heapq.heappop(h); seen += 1
        g = 2 ** L * bn - 3 ** n * bd                             # window: c * g < rho * bd
        if r * g >= tail[0] * bd: break                           # no c >= r can win any more
        if 3 ** j < 2 ** l:
            if j == n and l == L:
                c = r if r > 1 else r + 2 ** L; d = T(c, L)
                if d * bd > bn * c: bn, bd, best = d, c, c
                elif r == 1: pass
            continue
        if j > n or n - j > L - 1 - l: continue
        if r * g >= (3 ** (n - j) * rho + tail[j]) * bd: continue
        for t in (0, 1):
            v = 3 ** j * t + b; r2 = r + t * 2 ** l
            if v & 1: heapq.heappush(h, (r2, j + 1, l + 1, (3 * v + 1) // 2, 3 * rho + 2 ** l))
            else: heapq.heappush(h, (r2, j, l + 1, v // 2, rho))
    return best, seen
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
for n in range(N0, N1 + 1):
    t0 = time.time(); c, s = boo(n)
    print(n, c, 'nodes', s, '%.2fs' % (time.time() - t0), flush=True)
