// B143/B145: ties of the best of the Order. For each Order n in [N1, N2], with the best c* known (a b-file
// "n c"), find every other class id c of Order n with T^L(c)/c >= T^L(c*)/c* (equal: a tie; greater: the
// given best is wrong, FAILED). Same tree and pruning as boo.py / boo_ties.py part 2, but non-strict and
// depth-first: the window is fixed by c*, so every node with a residue inside its own window bound is
// visited, in any order, with memory O(L). Exact integers (GMP) throughout.
// Node (letter l, ones j, residue r < 2^l, b = T^l(r), rho_j). A class id below has c >= r and
// rho <= 3^(n-j) rho_j + tail_j (the wall after j ones), so with g = 2^L d* - 3^n c* > 0 it can tie or
// beat c* only if r g <= (3^(n-j) rho_j + tail_j) c*.
// Compile: g++ -O3 -std=c++17 boo_ties.cpp -o boo_ties -I/opt/homebrew/include -L/opt/homebrew/lib -lgmpxx -lgmp
// Run:     ./boo_ties N1 N2 bests_file progress_file   (an Order not yet in bests_file: re-read every 10 min)
// Output:  stdout and progress_file (appended, UTC-timestamped): a start line, one line per Order (nodes,
//          ties, seconds), a heartbeat every 10 minutes (Order, nodes so far), DONE or FAILED.
#include <gmpxx.h>
#include <chrono>
#include <cstdio>
#include <ctime>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

static std::string prog_file;
static void logline(const std::string &msg) {
    char ts[32]; std::time_t t = std::time(nullptr);
    std::strftime(ts, sizeof ts, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
    std::string line = std::string(ts) + " " + msg;
    std::cout << line << std::endl;
    if (!prog_file.empty()) { std::ofstream f(prog_file, std::ios::app); f << line << "\n"; }
}

static int p2(int m) { mpz_class x; mpz_ui_pow_ui(x.get_mpz_t(), 3, m); return (int)mpz_sizeinbase(x.get_mpz_t(), 2); }

int main(int argc, char **argv) {
    if (argc < 5) { std::cerr << "usage: boo_ties N1 N2 bests_file progress_file\n"; return 2; }
    int N1 = std::atoi(argv[1]), N2 = std::atoi(argv[2]);
    prog_file = argv[4];
    std::map<int, mpz_class> best;
    auto read_bests = [&]() {
        std::ifstream f(argv[3]); std::string s;
        while (std::getline(f, s)) { if (s.empty() || s[0] == '#') continue;
            std::istringstream is(s); int n; std::string c; if (is >> n >> c) best[n] = mpz_class(c); } };
    read_bests();
    logline("start boo_ties " + std::string(argv[1]) + " " + argv[2] + " " + argv[3]);
    auto t_last = std::chrono::steady_clock::now();
    for (int n = N1; n <= N2; ++n) {
        if (!best.count(n)) {                                    // the scan has not made Order n final yet:
            logline("waiting for the best of Order " + std::to_string(n) + " in " + argv[3]);
            while (!best.count(n)) { std::this_thread::sleep_for(std::chrono::minutes(10)); read_bests(); }
        }
        auto t0 = std::chrono::steady_clock::now();
        const int L = p2(n);
        std::vector<mpz_class> P3(n + 1), P2(L + 1), tail(n + 2);
        for (int i = 0; i <= n; ++i) mpz_ui_pow_ui(P3[i].get_mpz_t(), 3, i);
        for (int i = 0; i <= L; ++i) mpz_ui_pow_ui(P2[i].get_mpz_t(), 2, i);
        tail[n] = 0; tail[n + 1] = 0;
        for (int o = n; o >= 1; --o) tail[o - 1] = tail[o] + P3[n - o] * P2[p2(o - 1) - 1];
        const mpz_class cb = best[n];
        // d* = T^L(c*) by the trajectory, with its word checked to be of Order n (drop exactly at L).
        mpz_class x = cb; int ones = 0; bool ok = true;
        for (int l = 0; l < L; ++l) {
            if (mpz_odd_p(x.get_mpz_t())) { x = (3 * x + 1) / 2; ++ones; } else x /= 2;
            if (l + 1 < L && P3[ones] < P2[l + 1]) ok = false;     // dropped before L
        }
        if (!ok || ones != n || !(P3[n] < P2[L])) { logline("FAILED best of Order " + std::to_string(n) + " has not an Order-n word"); return 1; }
        const mpz_class db = x, g = P2[L] * db - P3[n] * cb;
        if (g <= 0) { logline("FAILED Order " + std::to_string(n) + ": ratio not above 3^n/2^L"); return 1; }
        // depth-first over (l, j, r, b, rho), one frame per letter
        struct F { int j; mpz_class r, b, rho; int next; };
        std::vector<F> st(L + 2);
        st[0] = {0, 0, 0, 0, 0};
        int depth = 0; unsigned long long nodes = 0; std::vector<std::string> ties;
        mpz_class lhs, rhs, v, c, d;
        bool enter = true;
        while (depth >= 0) {
            F &f = st[depth];
            const int l = depth;
            if (enter) {
                enter = false; ++nodes; f.next = 2;                  // default: no children
                if (l >= 1 && P3[f.j] < P2[l]) {                     // dropped at l
                    if (f.j == n && l == L) {
                        c = f.r > 1 ? mpz_class(f.r) : mpz_class(f.r + P2[L]);
                        if (c != cb) {
                            d = (P3[n] * c + f.rho) / P2[L];
                            lhs = d * cb; rhs = db * c;
                            if (lhs > rhs) { logline("FAILED Order " + std::to_string(n) + ": " + c.get_str() + " beats the given best"); return 1; }
                            if (lhs == rhs) ties.push_back(c.get_str());
                        }
                    }
                } else if (f.j <= n && n - f.j <= L - 1 - l) {
                    lhs = f.r * g; rhs = (P3[n - f.j] * f.rho + tail[f.j]) * cb;
                    if (lhs <= rhs) f.next = 0;                      // inside the window: visit both children
                }
                if ((nodes & 0xFFFFF) == 0) {
                    auto now = std::chrono::steady_clock::now();
                    if (now - t_last > std::chrono::minutes(10)) {
                        t_last = now;
                        logline("Order " + std::to_string(n) + " of " + std::to_string(N2) + ": " + std::to_string(nodes) + " nodes so far");
                    }
                }
            }
            if (f.next < 2) {
                int t = f.next++;
                F &ch = st[depth + 1];
                v = P3[f.j] * t + f.b;
                ch.r = f.r + (t ? P2[l] : mpz_class(0));
                if (mpz_odd_p(v.get_mpz_t())) { ch.j = f.j + 1; ch.b = (3 * v + 1) / 2; ch.rho = 3 * f.rho + P2[l]; }
                else { ch.j = f.j; ch.b = v / 2; ch.rho = f.rho; }
                ++depth; enter = true;
            } else {
                --depth;
            }
        }
        double sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
        std::string tl = ties.empty() ? "no tie" : "TIE";
        for (auto &s : ties) tl += " " + s;
        char buf[64]; std::snprintf(buf, sizeof buf, " (%.1fs)", sec);
        logline("Order " + std::to_string(n) + " best " + cb.get_str() + " nodes " + std::to_string(nodes) + ": " + tl + buf);
    }
    logline("DONE Orders " + std::to_string(N1) + ".." + std::to_string(N2));
    return 0;
}
