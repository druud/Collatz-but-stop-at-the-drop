// The two slow checks of paper_numbers.py, exact, with the same OK / DIFF / SKIP lines:
//   1. Table 1 of the paper "The best of the Order": k0 for Orders 2..21, over all words.
//   2. Remark "Cost": the nodes of the best-first search seeded with the smallest start, Orders 1..124
//      (as boo.py: nodes popped by residue), and its bests against data/best_cert_378.txt.
//   3. Appendix A: the same search with a first ratio guessed from the previous Order, Orders 2..75.
// Compile: mkdir -p _tmp; g++ -O3 -std=c++17 scripts/paper_numbers_slow.cpp -o _tmp/paper_numbers_slow \
//            -I/opt/homebrew/include -L/opt/homebrew/lib -lgmpxx -lgmp
// Run from Lean/best_of_order:  _tmp/paper_numbers_slow [FILE]
//   or _tmp/paper_numbers_slow --k0=N: k0 for Orders 22..N (N <= 32), against Table 1 up to 28 (22..25 about 5 minutes),
//   beyond it new; about 3 times the time per Order (26: some 10 minutes, 28: some 1.5 hours), one thread.
//   FILE: the b-file of A122442 (a(n+1) = the smallest start of Order n), data/b122442.txt by default;
//   if it cannot be read, only Table 1 is checked. One thread, about 2 minutes; memory: the heap of the search, about 2.4 GB at its peak.
// Integers only: Table 1 in u64 / i128 from exact tables (Orders to 21, checked), the search in GMP.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

using u64  = uint64_t;
using u128 = unsigned __int128;
using i128 = __int128;

static int nok = 0, ndiff = 0, nskip = 0;
static auto t00 = std::chrono::steady_clock::now();
static double secs() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - t00).count(); }

template <class A, class B> static void check(const std::string &what, const A &got, const B &paper) {
    std::ostringstream g, p;
    g << got; p << paper;
    bool ok = g.str() == p.str();
    (ok ? nok : ndiff)++;
    std::cout << (ok ? "OK   " : "DIFF ") << what << ": " << g.str();
    if (!ok) std::cout << "   (paper: " << p.str() << ")";
    std::cout << std::endl;
}

static int p2(int n) {                         // bit length of 3^n
    mpz_class t;
    mpz_ui_pow_ui(t.get_mpz_t(), 3, n);
    return (int)mpz_sizeinbase(t.get_mpz_t(), 2);
}

// ---------- 1. Table 1: k0, Orders 2..21 ----------
static u64 P3[41], P2[65];                     // exact tables: 3^j (j <= 40), 2^l (l <= 63)
static int N1, L1;                             // the Order and its word length
static u64 cb, rb, wb;                         // the best: class id, constant, word
static i128 sb[64];                            // c_best S_k of the best, k = 1..L
static int  last;                              // the largest k at which the best is not the strict maximum
static u64  nwords;
static int  pass;

static void sums(u64 c, u64 w, i128 *out) {    // out[k-1] = c_best S_k(c), k = 1..L
    int  ones = __builtin_popcountll(w);
    i128 s = 0;
    for (int l = L1 - 1; l >= 0; l--) {        // ones = the ones up to and including letter l
        int  e = (int)(w >> l & 1);
        i128 t = (e ? (i128)P3[N1 - ones] * cb : 0) - ((c >> l & 1) ? (i128)rb : 0);
        s += t * (i128)P2[l];
        ones -= e;
        out[L1 - 1 - l] = s;
    }
}

static void leaf(u64 c, u64 rho, u64 w) {
    if (pass == 1) {
        nwords++;
        u128 a = (u128)rho * cb, b = (u128)rb * c;          // rho/c against rb/cb
        if (cb == 0 || a > b || (a == b && c < cb)) { cb = c; rb = rho; wb = w; }
        return;
    }
    if (c == cb) return;
    i128 so[64];
    sums(c, w, so);
    for (int k = L1; k > last; k--)
        if (so[k - 1] >= sb[k - 1]) { last = k; break; }
}

// prefixes with 3^j > 2^l; node: residue r, ones j, letters l, b = T^l(r), rho_j, word bits
static void dfs(u64 r, int j, int l, u64 b, u64 rho, u64 w) {
    if (P3[j] < P2[l]) {
        if (j == N1 && l == L1) leaf(r, rho, w);
        return;
    }
    if (j > N1 || l >= L1) return;
    for (int t = 0; t < 2; t++) {
        u64 v = (t ? P3[j] : 0) + b, r2 = r + (t ? P2[l] : 0);
        if (v & 1) dfs(r2, j + 1, l + 1, (3 * v + 1) / 2, 3 * rho + P2[l], w | P2[l]);
        else       dfs(r2, j, l + 1, v / 2, rho, w);
    }
}

static int k0_of(int n) {
    N1 = n; L1 = p2(n);
    cb = rb = wb = 0; nwords = 0; last = 0;
    pass = 1; dfs(1, 1, 1, 2, 1, 1);
    {   // |c_best S_k| < 2^L max(3^n c_best, rb) <= 2^L 3^n max(c_best, n), as rb <= R(n) <= n 3^(n-1)
        mpz_class bound; mpz_ui_pow_ui(bound.get_mpz_t(), 3, n);
        bound *= (unsigned long)std::max<u64>(cb, (u64)n); bound <<= L1;
        if (mpz_sizeinbase(bound.get_mpz_t(), 2) > 126) return -1;     // the i128 sums could overflow
    }
    sums(cb, wb, sb);
    pass = 2; dfs(1, 1, 1, 2, 1, 1);
    return last + 1;
}

// ---------- 2. the best-first search, as boo.py ----------
struct Node {
    mpz_class r, b, rho;
    int       j, l;
};
struct ByR {
    bool operator()(const Node &x, const Node &y) const { return x.r > y.r; }   // min-heap on r
};

static mpz_class T_iter(mpz_class x, int L) {
    for (int i = 0; i < L; i++) {
        if (mpz_odd_p(x.get_mpz_t())) x = (3 * x + 1) / 2;
        else x /= 2;
    }
    return x;
}

// seed > 0: the first ratio is that of the start seed (attained). seed = 0: the first ratio is the guess
// gn/gd (boo_guess.py); the best returned is 0 if no word beats it.
static std::pair<mpz_class, u64> boo(int n, const mpz_class &seed, const mpz_class &gn = 0, const mpz_class &gd = 1) {
    int L = p2(n);
    std::vector<mpz_class> p3(n + 2), pw2(L + 2), tail(n + 2);
    p3[0] = 1; for (int i = 1; i <= n + 1; i++) p3[i] = p3[i - 1] * 3;
    pw2[0] = 1; for (int i = 1; i <= L + 1; i++) pw2[i] = pw2[i - 1] * 2;
    tail[n] = 0; tail[n + 1] = 0;
    for (int o = n; o >= 1; o--) tail[o - 1] = tail[o] + p3[n - o] * pw2[p2(o - 1) - 1];
    mpz_class bd = seed, bn, best = seed;
    if (seed > 0) bn = T_iter(seed, L); else { bn = gn; bd = gd; }
    mpz_class g = pw2[L] * bn - p3[n] * bd, lim0 = tail[0] * bd, t1, t2;
    u64 seen = 0;
    std::vector<Node> h;
    h.push_back({1, 2, 1, 1, 1});
    while (!h.empty()) {
        std::pop_heap(h.begin(), h.end(), ByR());
        Node x = std::move(h.back());
        h.pop_back();
        seen++;
        t1 = x.r * g;
        if (t1 >= lim0) break;                              // no c >= r can win any more
        if (p3[x.j] < pw2[x.l]) {
            if (x.j == n && x.l == L) {
                mpz_class c = x.r > 1 ? x.r : mpz_class(x.r + pw2[L]), d = T_iter(c, L);
                if (d * bd > bn * c) {
                    bn = d; bd = c; best = c;
                    g = pw2[L] * bn - p3[n] * bd; lim0 = tail[0] * bd;
                }
            }
            continue;
        }
        if (x.j > n || n - x.j > L - 1 - x.l) continue;
        t2 = (p3[n - x.j] * x.rho + tail[x.j]) * bd;
        if (t1 >= t2) continue;
        for (int t = 0; t < 2; t++) {
            Node y;
            mpz_class v = x.b;
            y.r = x.r;
            if (t) { v += p3[x.j]; y.r += pw2[x.l]; }
            y.l = x.l + 1;
            if (mpz_odd_p(v.get_mpz_t())) { y.j = x.j + 1; y.b = (3 * v + 1) / 2; y.rho = 3 * x.rho + pw2[x.l]; }
            else                          { y.j = x.j;     y.b = v / 2;           y.rho = x.rho; }
            h.push_back(std::move(y));
            std::push_heap(h.begin(), h.end(), ByR());
        }
    }
    return {best, seen};
}

int main(int argc, char **argv) {
    P3[0] = 1; for (int i = 1; i <= 40; i++) P3[i] = P3[i - 1] * 3;     // 3^40 < 2^64
    P2[0] = 1; for (int i = 1; i <= 63; i++) P2[i] = P2[i - 1] * 2;

    if (argc > 1 && std::string(argv[1]).rfind("--k0=", 0) == 0) {   // Table 1 beyond Order 21 (not in the default run: long)
        int N = std::atoi(argv[1] + 5);
        if (N < 22 || N > 32) { std::cerr << "--k0=N needs 22 <= N <= 32 (u64 nodes; Order 32 would take days)\n"; return 2; }
        std::map<int, std::string> bf;
        std::ifstream fb("data/b402443_378.txt");
        for (std::string line; std::getline(fb, line);) {
            std::istringstream is(line); int k; std::string v;
            if (line.empty() || line[0] == '#') continue;
            if (is >> k >> v) bf[k] = v;
        }
        const int K0b[7] = {25, 24, 29, 29, 30, 31, 32};   // Table 1, Orders 22..28
        std::cout << "--- Chapter 7: Table 1, k0 for Orders 22.." << N << " (and L/2 < k0 < 4L/5)" << std::endl;
        for (int n = 22; n <= N; n++) {
            int k = k0_of(n), L = p2(n);
            if (k < 0) { std::cout << "SKIP Order " << n << " and up: the i128 sums could overflow (best " << cb << ")" << std::endl; nskip++; break; }
            std::cout << "     Order " << n << ": " << nwords << " words, best " << cb << ", L = " << L << ", k0 = " << k
                      << " (" << (long)secs() << " s)" << std::endl;
            check("Order " + std::to_string(n) + ": the best equals the b-file of A402443", std::to_string(cb), bf[n]);
            if (n <= 28) check("Table 1: k0 for Order " + std::to_string(n), std::to_string(k), std::to_string(K0b[n - 22]));
            check("Order " + std::to_string(n) + ": L/2 < k0 < 4L/5", (L < 2 * k && 5 * k < 4 * L) ? "yes" : "no", "yes");
        }
        std::cout << "--- " << nok << " OK, " << ndiff << " DIFF, " << nskip << " SKIP (" << (long)secs() << " s)" << std::endl;
        return ndiff ? 1 : 0;
    }

    std::cout << "--- Chapter 7: backward ranking (Table 1)" << std::endl;
    const int K0[20] = {1, 1, 3, 2, 6, 4, 8, 7, 9, 9, 12, 13, 19, 14, 16, 16, 18, 24, 21, 23};
    std::ostringstream got, paper;
    for (int n = 2; n <= 21; n++) {
        int k = k0_of(n);
        got << (n > 2 ? " " : "") << k;
        paper << (n > 2 ? " " : "") << K0[n - 2];
        if (n >= 17)
            std::cout << "     Order " << n << ": " << nwords << " words, best " << cb << ", k0 = " << k << " ("
                      << (long)secs() << " s)" << std::endl;
    }
    check("Table 1: k0 for Orders 2..21", got.str(), paper.str());

    std::cout << "--- Chapter 6: the cost of the best-first search" << std::endl;
    const char *seedf = argc > 1 ? argv[1] : "data/b122442.txt";
    std::ifstream fs(seedf);
    if (!fs) {
        nskip++;
        std::cout << "SKIP the best-first search and its node counts: cannot read " << seedf << std::endl;
    } else {
        std::map<int, mpz_class> seed, cert;
        std::string line;
        std::ifstream fc("data/best_cert_378.txt");
        if (!fc) { std::cerr << "cannot read data/best_cert_378.txt\n"; return 2; }
        while (std::getline(fs, line)) {
            if (line.empty() || line[0] == '#') continue;
            std::istringstream is(line);
            int k; std::string v;
            if (is >> k >> v && k >= 2) seed[k - 1] = mpz_class(v);
        }
        while (std::getline(fc, line)) {
            if (line.empty() || line[0] == '#') continue;
            std::istringstream is(line);
            int n; std::string c;
            if (is >> n >> c) cert[n] = mpz_class(c);
        }
        mpz_class tot = 0;
        u64 s124 = 0;
        std::string wrong;
        for (int n = 1; n <= 124; n++) {
            auto [b, s] = boo(n, seed[n]);
            tot += (unsigned long)s;
            if (n == 124) s124 = s;
            if (b != cert[n]) wrong += " " + std::to_string(n);
            if (n % 10 == 0 || n == 124)
                std::cout << "     Order " << n << ": " << s << " nodes, " << tot << " so far (" << (long)secs()
                          << " s)" << std::endl;
        }
        check("best-first search, Orders 1..124: Orders with another best than the certificate file", "[" + wrong + "]", "[]");
        check("best-first search, Orders 1..124: nodes in all", tot, "164801730");
        check("best-first search, Order 124: nodes", s124, "15147961");

        // Appendix A: the first ratio guessed from theta of the previous Order, halved until a word beats it
        mpq_class theta(1, 2);
        mpz_class tg = 0, ts = 0;
        std::string wrong2;
        for (int n = 2; n <= 75; n++) {
            int L = p2(n);
            mpz_class p3n, p2L;
            mpz_ui_pow_ui(p3n.get_mpz_t(), 3, n);
            mpz_ui_pow_ui(p2L.get_mpz_t(), 2, L);
            mpq_class th = theta, lvl(p3n, p2L);
            lvl.canonicalize();
            mpz_class c;
            while (true) {
                mpq_class q = lvl + th * (1 - lvl);
                auto [b, s] = boo(n, 0, q.get_num(), q.get_den());
                tg += (unsigned long)s;
                if (b > 0) { c = b; break; }
                th /= 2;
            }
            if (c != cert[n]) wrong2 += " " + std::to_string(n);
            mpz_class d = T_iter(c, L);
            theta = mpq_class(p2L * d - p3n * c, c * (p2L - p3n));
            theta.canonicalize();
            ts += (unsigned long)boo(n, seed[n]).second;
        }
        check("guessed first ratio, Orders 2..75: Orders with another best than the certificate file", "[" + wrong2 + "]", "[]");
        check("guessed first ratio, Orders 2..75: nodes in all", tg, "8408907");
        check("seeded with the smallest start, Orders 2..75: nodes in all", ts, "4317574");
    }
    std::cout << "--- " << nok << " OK, " << ndiff << " DIFF, " << nskip << " SKIP (" << (long)secs() << " s)" << std::endl;
    return ndiff ? 1 : 0;
}
