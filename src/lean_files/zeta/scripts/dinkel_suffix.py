# B121/B130: the backward ranking at lam* (dinkel.py, part 2), exact, all words by the admissible-prefix tree.
# Per Order n: G(c) = rho - lam* c = sum_l 2^l delta_l, delta_l = e_l 3^(n-w_l) - lam* t_l (w_l the ones up to and
# including letter l, so n - w_l = the ones after l; t_l bit l of c). Suffix sums S_k(c) = sum over the last k
# letters. Reported: k0, the least k such that the best is the strict maximum of S_k for every k >= k0, and the
# start letter L - k0. Integers only: everything times c_best. Words as bit masks (lean on memory).
# Usage: dinkel_suffix.py n_from n_to [progress_file]
import sys, time
from fractions import Fraction
p2 = lambda m: (3**m).bit_length()
PROG = sys.argv[3] if len(sys.argv) > 3 else None
def log(msg):
    line = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()) + ' ' + msg
    print(line, flush=True)
    if PROG:
        with open(PROG, 'a') as f: f.write(line + '\n')
def words(n):
    L = p2(n); C, E = [], []
    st = [(0, 0, 0, 0, 0)]                                   # (r, j, l, b = T^l(r), letter mask)
    while st:
        r, j, l, b, e = st.pop()
        if l == L:
            if j == n and 3**j < 2**l: C.append(r if r > 1 else r + 2**L); E.append(e)
            continue
        if l >= 1 and 3**j < 2**l: continue                  # dropped before L
        if j > n: continue
        for t in (0, 1):
            v = 3**j * t + b
            if v & 1: st.append((r + t * 2**l, j + 1, l + 1, (3*v + 1) // 2, e | 1 << l))
            else: st.append((r + t * 2**l, j, l + 1, v // 2, e))
    return L, C, E
try:
    log('start dinkel_suffix.py %s' % ' '.join(sys.argv[1:]))
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        t0 = time.time()
        L, C, E = words(n); N = len(C)
        def rho(e):
            s = 0; w = 0
            for l in range(L):
                if e >> l & 1: w += 1; s += 3**(n - w) * 2**l
            return s
        ib = max(range(N), key=lambda i: Fraction(rho(E[i]), C[i]))
        cb, rb = C[ib], rho(E[ib])
        after = [0] * N; suf = [0] * N; strict = []
        p3 = [3**a * cb for a in range(n + 1)]                   # 3^(n - w_l) at a one: a = n - w_l, the ones after l
        for k in range(1, L + 1):                            # add letter l = L - k: c_best * delta_l * 2^l
            l = L - k
            for i in range(N):
                e = E[i] >> l & 1
                suf[i] += ((p3[after[i]] if e else 0) - rb * (C[i] >> l & 1)) << l
                after[i] += e
            sb = suf[ib]
            strict.append(all(suf[i] < sb for i in range(N) if i != ib))
        k0 = L + 1
        while k0 > 1 and strict[k0 - 2]: k0 -= 1
        log('Order %d L %d words %d best %d: strict max for all suffixes of k >= %d letters, from letter %d (%.0fs)'
            % (n, L, N, cb, k0, L - k0, time.time() - t0))
    log('DONE')
except BaseException as ex:
    log('FAILED %r' % ex); raise
