// Remark "Both sides in turns" and open question 5 of the paper "The best of the Order", past mitm4.py:
// over all words of Order n, at lambda = lambda* (the best's rho/c), cut each word after its w-th one
// (w = 1..n-1) into a start side A and a drop side B, G = A + B = rho - lambda c. A word can be the best
// only if A + max B >= 0 and B + max A >= 0 (maxima over the Order's words at that w); per w the number of
// words that pass both tests. Same numbers as mitm4.py (checked for Orders 4..13), in integers:
//   3^w c* A = rp (3^n c* + rho*),   3^w c* B = (rho - 3^(n-w) rp) 3^w c* - rho* (3^w c + rp),
// rp the constant of the first m letters (m after the w-th one), as 2^m T^m(c) = 3^w c + rp.
// Compile: mkdir -p _tmp; g++ -O3 -std=c++17 scripts/both_sides.cpp -o _tmp/both_sides \
//            -I/opt/homebrew/include -L/opt/homebrew/lib -lgmpxx -lgmp
// Run from Lean/accelerated_collatz/zeta:  _tmp/both_sides n1 n2   (one thread; three passes over the words of each
//   Order; the words grow about 2.7 times per Order). An Order whose i128 values could overflow is SKIPped.
#include <gmpxx.h>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

using u64 = uint64_t;
using u128 = unsigned __int128;
using i128 = __int128;

static u64 P3[41], P2[64];
static int N, L;
static u64 cb, rb;                                   // the best: class id, constant
static i128 K;                                       // 3^n c* + rho*
static i128 mA[64], mB[64];                          // the maxima per cut w
static bool seen[64];
static u64 kept[64], nwords;
static int pass;

static int p2(int n) {
    mpz_class t;
    mpz_ui_pow_ui(t.get_mpz_t(), 3, n);
    return (int)mpz_sizeinbase(t.get_mpz_t(), 2);
}

// the two sides of the word (class id c, constant rho, letters w) at every cut; f(w, A, B)
template <class Fn> static void sides(u64 c, u64 rho, u64 w, Fn f) {
    u64 rp = 0; int q = 0;
    for (int k = 0; k < L && q < N - 1; k++) {
        if (!(w >> k & 1)) continue;
        rp = 3 * rp + P2[k]; q++;
        i128 A = (i128)rp * K;
        i128 B = ((i128)rho - (i128)P3[N - q] * rp) * (i128)P3[q] * (i128)cb - (i128)rb * ((i128)P3[q] * c + rp);
        f(q, A, B);
    }
}

static void leaf(u64 c, u64 rho, u64 w) {
    if (pass == 1) {
        nwords++;
        u128 a = (u128)rho * cb, b = (u128)rb * c;
        if (cb == 0 || a > b || (a == b && c < cb)) { cb = c; rb = rho; }
    } else if (pass == 2) {
        sides(c, rho, w, [](int q, i128 A, i128 B) {
            if (!seen[q] || A > mA[q]) mA[q] = A;
            if (!seen[q] || B > mB[q]) mB[q] = B;
            seen[q] = true;
        });
    } else {
        sides(c, rho, w, [](int q, i128 A, i128 B) {
            if (A + mB[q] >= 0 && B + mA[q] >= 0) kept[q]++;
        });
    }
}

// prefixes with 3^j > 2^l; node: residue r, ones j, letters l, b = T^l(r), rho_j, word bits
static void dfs(u64 r, int j, int l, u64 b, u64 rho, u64 w) {
    if (P3[j] < P2[l]) {
        if (j == N && l == L) leaf(r, rho, w);
        return;
    }
    if (j > N || l >= L) return;
    for (int t = 0; t < 2; t++) {
        u64 v = (t ? P3[j] : 0) + b, r2 = r + (t ? P2[l] : 0);
        if (v & 1) dfs(r2, j + 1, l + 1, (3 * v + 1) / 2, 3 * rho + P2[l], w | P2[l]);
        else       dfs(r2, j, l + 1, v / 2, rho, w);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { std::cerr << "usage: both_sides n1 n2  (4 <= n1 <= n2 <= 32)\n"; return 2; }
    int n1 = std::atoi(argv[1]), n2 = std::atoi(argv[2]);
    if (n1 < 4 || n2 > 32 || n1 > n2) { std::cerr << "needs 4 <= n1 <= n2 <= 32 (u64 nodes)\n"; return 2; }
    P3[0] = 1; for (int i = 1; i <= 40; i++) P3[i] = P3[i - 1] * 3;
    P2[0] = 1; for (int i = 1; i <= 63; i++) P2[i] = P2[i - 1] * 2;
    auto t0 = std::chrono::steady_clock::now();
    auto secs = [&] { return (long)std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); };
    for (N = n1; N <= n2; N++) {
        L = p2(N); cb = rb = 0; nwords = 0;
        std::fill(seen, seen + 64, false); std::fill(kept, kept + 64, 0);
        pass = 1; dfs(1, 1, 1, 2, 1, 1);
        {   // |A|, |B| <= n 3^(2n-2) (3 c* + 2^L + n), as rho <= R(n) <= n 3^(n-1), rp <= R(w), w <= n-1, c < 2^L:
            // so the sums A + max B, B + max A stay below 2 n 3^(2n-2) (3 c* + 2^L + 2n) < 2^127
            mpz_class t, tL, b;
            mpz_ui_pow_ui(t.get_mpz_t(), 3, 2 * N - 2);
            mpz_ui_pow_ui(tL.get_mpz_t(), 2, L);
            b = 2 * N * t * (3 * (unsigned long)cb + tL + 2 * N);
            if (mpz_sizeinbase(b.get_mpz_t(), 2) > 127) {
                std::cout << "SKIP Order " << N << " and up: the i128 values could overflow" << std::endl;
                break;
            }
        }
        K = (i128)P3[N] * cb + rb;
        pass = 2; dfs(1, 1, 1, 2, 1, 1);
        pass = 3; dfs(1, 1, 1, 2, 1, 1);
        u64 lo = ~0ULL, hi = 0;
        std::string per;
        for (int q = 1; q < N; q++) {
            lo = std::min(lo, kept[q]); hi = std::max(hi, kept[q]);
            per += " " + std::to_string(q) + ":" + std::to_string(kept[q]);
        }
        std::cout << "Order " << N << " (" << nwords << " words) best " << cb << "  words kept per cut, "
                  << lo << " to " << hi << ":" << per << "  (" << secs() << " s)" << std::endl;
    }
    std::cout << "DONE (" << secs() << " s)" << std::endl;
}
