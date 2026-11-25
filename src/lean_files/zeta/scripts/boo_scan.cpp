// Best of the Order: per Order n = 1..N, the class id c > 1 with the highest drop ratio T^L(c)/c,
// L = p2(n) = bit length of 3^n (B120; boo.py does the same by best-first search, Orders 1..124).
// From a122442_search_03.cpp: the same wheel and scan over x0 in increasing rounds, now keeping
// per Order the highest ratio d/x0 (d = the drop value) instead of the smallest x0.
// Every x0 of a class has a ratio at most that of its class id, so the best over all x0 is a
// class id. Orders with p2(n) <= W are solved exactly in the wheel; the others by the scan.
// Window: 2^L d = 3^n c + rho with rho <= R = sum_{o=1..n} 3^(n-o) 2^(p2(o-1)-1) (the wall
// word), so c beats the best bn/bd only if c (2^L bn - 3^n bd) < R bd. An Order is final once
// all x0 below win = ceil(R bd / (2^L bn - 3^n bd)) are scanned.
// Seed: the A122442 b-file (a(n+1) = the smallest start value of Order n): its ratios give
// every window from the first round, so the scan bound needed is known from the start; the
// first x0 of each Order met by the scan is checked against it.
// Compile:  g++ -O3 -march=native -std=c++17 -pthread boo_scan.cpp -o boo_scan
// Run:      ./boo_scan [--seed=b122442.txt] [--progress=boo_scan.progress]
//                      [--resume=boo_scan.progress.state] <N> [W=28] [threads] > boo_scan.out
// Output: a b-file on stdout, "n c" (c = the best of Order n), written as soon as Orders 1..n
// are final; "# " comment lines on top (command, SHA-256 of the executable, compiler, system,
// CPU, settings, start time UTC) and at the bottom (end time, wall time, scan bound, checks,
// and per Order "# n c T^L(c) window"). Every best is checked by its exact trajectory: drop
// Order n and drop value T^L(c).
// Progress: stderr, one line per round; the progress file gets a UTC-timestamped line about
// every 10 minutes (scan bound, needed bound, per mille done, Orders final) and DONE or FAILED
// at the end; FILE.state is overwritten with it (scan state and bests, for --resume).
// Width identity: the scan follows each x0 to its drop and counts the prefixes with 3^j < 2^l
// (j ones in l letters) at which the value is not below x0. With a count of 0 the drop of every
// x0 scanned is at its first such prefix, so the Orders reported do not rest on the width
// identity (a resumed run counts from the resume on). A count above 0 is reported as FAILED.
// Integers only: u128 in the scan (overflow guard: an exact multiword slow path), exact
// multiword integers for 3^n, R and the windows.

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

#include <unistd.h>

#include <sys/utsname.h>
#ifdef __APPLE__
#include <sys/sysctl.h>
#endif

using u64  = uint64_t;
using u32  = uint32_t;
using u128 = __uint128_t;

static const u64 NONE = ~0ull;

// ---------- the run environment, for the comment lines of the b-file ----------
// SHA-256 (FIPS 180-4) of a byte string, as 64 hex digits.
static std::string sha256_hex(const std::string &msg) {
    static const u32 K[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2};
    std::array<u32, 8> h = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                            0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    auto rotr = [](u32 x, int n) { return (x >> n) | (x << (32 - n)); };
    std::string m   = msg;
    u64         bit = (u64)msg.size() * 8;
    m += (char)0x80;
    while (m.size() % 64 != 56) m += (char)0;
    for (int i = 7; i >= 0; i--) m += (char)(bit >> (8 * i));
    for (size_t off = 0; off < m.size(); off += 64) {
        u32 w[64];
        for (int i = 0; i < 16; i++) {
            const unsigned char *p = (const unsigned char *)m.data() + off + 4 * i;
            w[i] = (u32)p[0] << 24 | (u32)p[1] << 16 | (u32)p[2] << 8 | p[3];
        }
        for (int i = 16; i < 64; i++) {
            u32 s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            u32 s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i]   = w[i - 16] + s0 + w[i - 7] + s1;
        }
        std::array<u32, 8> a = h;
        for (int i = 0; i < 64; i++) {
            u32 S1 = rotr(a[4], 6) ^ rotr(a[4], 11) ^ rotr(a[4], 25);
            u32 ch = (a[4] & a[5]) ^ (~a[4] & a[6]);
            u32 t1 = a[7] + S1 + ch + K[i] + w[i];
            u32 S0 = rotr(a[0], 2) ^ rotr(a[0], 13) ^ rotr(a[0], 22);
            u32 mj = (a[0] & a[1]) ^ (a[0] & a[2]) ^ (a[1] & a[2]);
            u32 t2 = S0 + mj;
            a      = {t1 + t2, a[0], a[1], a[2], a[3] + t1, a[4], a[5], a[6]};
        }
        for (int i = 0; i < 8; i++) h[i] += a[i];
    }
    static const char *hex = "0123456789abcdef";
    std::string        out;
    for (u32 x : h)
        for (int i = 28; i >= 0; i -= 4) out += hex[(x >> i) & 15];
    return out;
}

// SHA-256 of the file at path, or "unreadable".
static std::string sha256_file(const char *path) {
    std::ifstream f(path, std::ios::binary);
    if (!f) return "unreadable";
    std::string s((std::istreambuf_iterator<char>(f)), std::istreambuf_iterator<char>());
    return sha256_hex(s);
}

// Printable ASCII only (b-files allow no other bytes).
static std::string ascii(const std::string &s) {
    std::string out;
    for (unsigned char ch : s) out += ch >= 32 && ch < 127 ? (char)ch : '?';
    return out;
}

// Current time in UTC as 2026-10-20T15:26:09Z.
static std::string utc_now() {
    std::time_t t = std::time(nullptr);
    char        buf[32];
    std::strftime(buf, sizeof buf, "%Y-%m-%dT%H:%M:%SZ", std::gmtime(&t));
    return buf;
}

// System name, release and machine (no host name).
static std::string system_name() {
    struct utsname u;
    if (uname(&u) != 0) return "unknown";
    return std::string(u.sysname) + " " + u.release + " " + u.machine;
}

// CPU model, or "unknown".
static std::string cpu_name() {
#ifdef __APPLE__
    char   buf[256];
    size_t len = sizeof buf;
    if (sysctlbyname("machdep.cpu.brand_string", buf, &len, nullptr, 0) == 0) return buf;
#else
    std::ifstream f("/proc/cpuinfo");
    std::string   line;
    while (std::getline(f, line))
        if (line.rfind("model name", 0) == 0) return line.substr(line.find(':') + 2);
#endif
    return "unknown";
}

// Seconds as h:mm:ss.
static std::string hms(double secs) {
    long               t = (long)(secs + 0.5);
    std::ostringstream o;
    o << t / 3600 << ":" << (t / 600) % 6 << (t / 60) % 10 << ":" << (t % 60) / 10 << t % 10;
    return o.str();
}

// ---------- p2_of(n) = bit length of 3^n, exact ----------
static std::vector<int> p2tab;

static void build_p2tab(int maxn) {
    std::vector<u64> v = {1};
    p2tab.assign(maxn + 1, 0);
    for (int n = 0; n <= maxn; n++) {
        if (n > 0) {
            u128 carry = 0;
            for (auto &w : v) {
                u128 p = (u128)w * 3 + carry;
                w      = (u64)p;
                carry  = p >> 64;
            }
            if (carry) v.push_back((u64)carry);
        }
        p2tab[n] = (int)(v.size() - 1) * 64 + (64 - __builtin_clzll(v.back()));
    }
}

// 3^o > 2^b  <=>  b < p2_of(o)
static inline bool adm(int o, int b) { return b < p2tab[o]; }

// ---------- exact nonnegative integers, 64-bit limbs, little endian ----------
using Big = std::vector<u64>;

static void trim(Big &a) { while (a.size() > 1 && a.back() == 0) a.pop_back(); }

static Big mul_small(const Big &a, u64 m) {
    Big  r(a.size() + 1);
    u128 carry = 0;
    for (size_t i = 0; i < a.size(); i++) {
        u128 p = (u128)a[i] * m + carry;
        r[i]   = (u64)p;
        carry  = p >> 64;
    }
    r[a.size()] = (u64)carry;
    trim(r);
    return r;
}

static Big shl(const Big &a, int s) {
    Big r(a.size() + s / 64 + 1, 0);
    int q = s / 64, b = s % 64;
    for (size_t i = 0; i < a.size(); i++) {
        r[i + q] |= a[i] << b;
        if (b) r[i + q + 1] |= a[i] >> (64 - b);
    }
    trim(r);
    return r;
}

static Big add(const Big &a, const Big &b) {
    Big  r(std::max(a.size(), b.size()) + 1, 0);
    u128 carry = 0;
    for (size_t i = 0; i + 1 < r.size(); i++) {
        u128 s = carry + (i < a.size() ? a[i] : 0) + (i < b.size() ? b[i] : 0);
        r[i]   = (u64)s;
        carry  = s >> 64;
    }
    r.back() = (u64)carry;
    trim(r);
    return r;
}

static int cmp(const Big &a, const Big &b) {
    if (a.size() != b.size()) return a.size() < b.size() ? -1 : 1;
    for (size_t i = a.size(); i-- > 0;)
        if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
}

static Big sub(const Big &a, const Big &b) {   // a >= b
    Big r(a.size());
    u64 borrow = 0;
    for (size_t i = 0; i < a.size(); i++) {
        u64  y = i < b.size() ? b[i] : 0;
        u128 d = (u128)a[i] - y - borrow;
        r[i]   = (u64)d;
        borrow = (u64)(d >> 64) ? 1 : 0;
    }
    trim(r);
    return r;
}

// ---------- per Order: 3^n, R(n), the best so far and its window ----------
struct Best {
    u64 c = 0;   // best class id (0: none yet)
    u64 d = 0;   // T^L(c)
};

static std::vector<Big> P3, RW;   // 3^n, R(n)
static const u64        INF = ~0ull;

// ceil(R bd / (2^L bn - 3^n bd)), or INF when it is 2^64 or more, or no best yet
static u64 window(int n, const Best &b) {
    if (b.c == 0) return INF;
    Big G = sub(shl(Big{b.d}, p2tab[n]), mul_small(P3[n], b.c));
    Big Y = mul_small(RW[n], b.c);
    if (cmp(mul_small(G, INF), Y) < 0) return INF;   // win > 2^64 - 1
    u64 lo = 0, hi = INF;                             // least X with X G >= Y
    while (lo < hi) {
        u64 mid = lo + (hi - lo) / 2;
        if (cmp(mul_small(G, mid), Y) >= 0) hi = mid; else lo = mid + 1;
    }
    return lo;
}

static inline bool better(u64 d, u64 c, const Best &b) {   // d/c > b.d/b.c
    return b.c == 0 || (u128)d * b.c > (u128)b.d * c;
}

// ---------- wheel: tree DFS over parity prefixes of length <= W ----------
// Node: residue r mod 2^j, x = r + 2^j*a  ->  T^j(x) = 3^o*a + t.
// A prefix failing admissibility at depth j closes a class of Order o (id r, r < 2: r + 2^j):
// its ratio is T^j(id)/id. Prefixes admissible through depth W are the wheel survivors.
struct Surv {
    u64     r;
    u64     t;
    uint8_t o;
};

static std::vector<Surv> surv;
static std::vector<Best> best;      // indexed by Order
static std::vector<u64>  first_id;  // smallest x0 met per Order (check against A122442)

static void dfs(u64 r, u64 t, int o, int j, int W, u64 p3o) {
    if (j == W) { surv.push_back({r, t, (uint8_t)o}); return; }
    for (int a0 = 0; a0 < 2; a0++) {
        u64 r2 = r + (a0 ? (1ull << j) : 0);
        u64 u  = t + (a0 ? p3o : 0);           // T^j value with a = 2a'+a0: 2*3^o*a' + u
        u64 t2;
        int o2;
        u64 p3o2;
        if (u & 1) { t2 = (3 * u + 1) / 2; o2 = o + 1; p3o2 = p3o * 3; }
        else       { t2 = u / 2;           o2 = o;     p3o2 = p3o;     }
        if (adm(o2, j + 1)) {
            dfs(r2, t2, o2, j + 1, W, p3o2);
        } else {
            u64 id = r2 < 2 ? r2 + (1ull << (j + 1)) : r2;   // skip trivial 0, 1
            u64 d  = r2 < 2 ? p3o2 + t2 : t2;                 // T^(j+1)(id)
            if (first_id[o2] == NONE || id < first_id[o2]) first_id[o2] = id;
            if (o2 > 0 && better(d, id, best[o2])) best[o2] = {id, d};
        }
    }
}

// ---------- 16-step jump table on the low bits ----------
constexpr int JK = 16;

struct Jump {
    uint8_t  ocum[JK];     // odd steps among steps 1..j+1
    uint32_t dj[JK + 1];   // T^j(w + 2^j*y) = 3^ocum[j-1]*y + dj[j]  (low j bits of w)
    uint16_t evmask;       // bit j set: step j+1 is even
};

static std::vector<Jump> jt;
static u64               pow3[41];     // 3^0..3^40: wheel survivors have o <= W <= 36

static void build_jt() {
    pow3[0] = 1;
    for (int i = 1; i < 41; i++) pow3[i] = pow3[i - 1] * 3;
    jt.resize(1u << JK);
    for (u64 w = 0; w < (1u << JK); w++) {
        Jump &e = jt[w];
        e.evmask = 0;
        e.dj[0]  = 0;
        for (int j = 1; j <= JK; j++) {        // dj[j] = T^j(w mod 2^j)
            u64 v = w & ((1ull << j) - 1);
            for (int k = 0; k < j; k++) v = (v & 1) ? (3 * v + 1) / 2 : v / 2;
            e.dj[j] = (uint32_t)v;
        }
        u64 v = w;
        int o = 0;
        for (int j = 0; j < JK; j++) {
            if (v & 1) { v = (3 * v + 1) / 2; o++; }
            else       { v /= 2; e.evmask |= (uint16_t)(1u << j); }
            e.ocum[j] = (uint8_t)o;
        }
    }
}

// ---------- exact slow path (big values) ----------
struct Drop {
    int o;   // odd steps up to the drop
    u64 d;   // drop value (< x0)
};

static std::atomic<u64> width_fail{0};   // prefixes with 3^o < 2^b at which the value is not below x0

static Drop drop_slow(u64 x0) {
    std::vector<u64> v = {x0};
    int              o = 0, b = 0;
    while (true) {
        if (v[0] & 1) {
            u128 carry = 1;                    // 3v+1
            for (auto &w : v) {
                u128 p = (u128)w * 3 + carry;
                w      = (u64)p;
                carry  = p >> 64;
            }
            if (carry) v.push_back((u64)carry);
            o++;
        }
        for (size_t i = 0; i < v.size(); i++) {  // v /= 2
            v[i] >>= 1;
            if (i + 1 < v.size()) v[i] |= v[i + 1] << 63;
        }
        if (v.size() > 1 && v.back() == 0) v.pop_back();
        b++;
        if (v.size() == 1 && v[0] < x0) return {o, v[0]};
        if (o >= (int)p2tab.size() || !adm(o, b)) width_fail++;
    }
}

static std::atomic<u64> slow_count{0};

// Order and drop value of x0 = 2^W*a + s.r, trajectory entering after W steps
static Drop drop_of(u64 x0, u64 a, const Surv &s, int W) {
    const u128 LIM_J = (u128)1 << 100;
    const u128 LIM_1 = (u128)1 << 125;
    u128       v     = (u128)pow3[s.o] * a + s.t;
    int        o     = s.o;
    int        b     = W;
    while (true) {
        if (v >= LIM_J) {
            if (v >= LIM_1) { slow_count++; return drop_slow(x0); }
            if (v & 1) { v = (3 * v + 1) / 2; o++; }
            else       { v /= 2; if (v < x0) return {o, (u64)v}; }
            b++;
            if (!adm(o, b)) width_fail++;
            continue;
        }
        const Jump &e = jt[(uint32_t)v & ((1u << JK) - 1)];
        int js = JK;                           // steps safe to jump
        if (b + JK >= p2tab[o]) {
            for (uint16_t m = e.evmask; m; m &= m - 1) {
                int j = __builtin_ctz(m);
                if (!adm(o + e.ocum[j], b + j + 1)) { js = j; break; }
            }
        }
        if (js > 0) {
            int c = e.ocum[js - 1];
            v  = (u128)pow3[c] * (v >> js) + e.dj[js];
            o += c;
            b += js;
        }
        if (js < JK) {                         // step js+1 is even and may drop
            v /= 2;
            b++;
            if (v < x0) return {o, (u64)v};
            width_fail++;                      // 3^o < 2^b, and no drop
        }
    }
}

int main(int argc, char **argv) {
    std::string              seedf = "b122442.txt", progf = "boo_scan.progress", resf;
    std::vector<std::string> pos;
    for (int i = 1; i < argc; i++) {
        std::string a = argv[i];
        if (a.rfind("--seed=", 0) == 0) seedf = a.substr(7);
        else if (a.rfind("--progress=", 0) == 0) progf = a.substr(11);
        else if (a.rfind("--resume=", 0) == 0) resf = a.substr(9);
        else pos.push_back(a);
    }
    if (pos.empty() || pos.size() > 3) {
        std::cerr << "usage: " << argv[0] << " [--seed=F] [--progress=F] [--resume=F.state] <N> [W=28] [threads]\n";
        return 1;
    }
    int N  = std::atoi(pos[0].c_str());
    int W  = pos.size() > 1 ? std::atoi(pos[1].c_str()) : 28;
    int NT = pos.size() > 2 ? std::atoi(pos[2].c_str()) : (int)std::thread::hardware_concurrency();
    if (NT < 1) NT = 1;
    if (W < 4 || W > 36 || N < 1) { std::cerr << "bad arguments\n"; return 1; }

    std::ofstream prog(progf, std::ios::app);
    if (!prog) { std::cerr << "cannot write " << progf << "\n"; return 1; }
    auto plog = [&](const std::string &s) { prog << utc_now() << " " << s << std::endl; };

    const auto t_start = std::chrono::steady_clock::now();
    std::cout << "# Best of the Order: n c, c > 1 the class id of Order n with the highest "
                 "T^L(c)/c, L = bit length of 3^n, by boo_scan\n# command:";
    for (int i = 0; i < argc; i++) std::cout << ' ' << ascii(argv[i]);
    std::cout << "\n# sha256 of the executable: " << sha256_file(argv[0])
              << "\n# compiler: " << ascii(__VERSION__)
              << "\n# system: " << ascii(system_name()) << "; CPU: " << ascii(cpu_name())
              << "\n# N=" << N << " W=" << W << " threads=" << NT
              << " (hardware: " << std::thread::hardware_concurrency() << ")"
              << "\n# seed: " << ascii(seedf) << " (sha256 " << sha256_file(seedf.c_str()) << ")"
              << "\n# started: " << utc_now() << std::endl;

    int maxo = std::max(N + 8, 2 * W) * 2 + 400;
    build_p2tab(maxo);
    P3.assign(maxo + 1, Big{1});
    RW.assign(maxo + 1, Big{0});
    for (int n = 1; n <= maxo; n++) {
        P3[n] = mul_small(P3[n - 1], 3);
        RW[n] = add(mul_small(RW[n - 1], 3), shl(Big{1}, p2tab[n - 1] - 1));
    }
    best.assign(maxo + 1, Best{});
    first_id.assign(maxo + 1, NONE);
    build_jt();
    dfs(0, 0, 0, 0, W, 1);
    std::sort(surv.begin(), surv.end(), [](const Surv &x, const Surv &y) { return x.r < y.r; });
    std::cerr << "W=" << W << " survivors=" << surv.size() << " threads=" << NT << "\n";
    std::cout << "# survivors mod 2^" << W << ": " << surv.size() << std::endl;
    int wheel_top = 0;                         // Orders 1..wheel_top: all words within the wheel
    while (p2tab[wheel_top + 1] <= W) wheel_top++;

    // seed: a(n+1) of A122442 is a start value of Order n
    std::vector<u64> seed(maxo + 1, 0);
    int              fails = 0, nseed = 0;
    {
        std::ifstream f(seedf);
        std::string   line;
        while (std::getline(f, line)) {
            if (line.empty() || line[0] == '#') continue;
            std::istringstream is(line);
            long long k;
            u64       v;
            if (!(is >> k >> v) || k < 2 || k - 1 > maxo) continue;
            int  n  = (int)(k - 1);
            Drop dr = drop_slow(v);
            if (dr.o != n) { std::cerr << "seed FAIL a(" << k << ")=" << v << " Order " << dr.o << "\n"; fails++; continue; }
            seed[n] = v;
            nseed++;
            if (better(dr.d, v, best[n])) best[n] = {v, dr.d};
        }
    }
    std::cerr << "seed: " << nseed << " start values from " << seedf << "\n";

    u64  A = 0, ROUND = 1;
    if (!resf.empty()) {                       // state: "W N A ROUND", then "n c d"
        std::ifstream f(resf);
        int           w2, n2;
        if (!(f >> w2 >> n2 >> A >> ROUND) || w2 != W) { std::cerr << "bad state file\n"; return 1; }
        int n;
        u64 c, d;
        while (f >> n >> c >> d)
            if (n >= 0 && n <= maxo && better(d, c, best[n])) best[n] = {c, d};
        std::cerr << "resumed at x0 < " << (A << W) << "\n";
        std::cout << "# resumed from " << ascii(resf) << " at x0 < " << (A << W) << std::endl;
        plog("resumed at x0 < " + std::to_string(A << W));
    }

    std::vector<u64> win(maxo + 1, INF);
    for (int n = 1; n <= N; n++) win[n] = n <= wheel_top ? 0 : window(n, best[n]);

    int done = 0;                              // Orders 1..done written
    auto flush = [&]() {
        u64 X = A << W;                        // all x0 < X scanned
        while (done < N && best[done + 1].c && win[done + 1] <= X) {
            int n = ++done;
            std::cout << n << " " << best[n].c << std::endl;
            Drop dr = drop_slow(best[n].c);
            if (dr.o != n || dr.d != best[n].d) {
                std::cerr << "FAIL n=" << n << " c=" << best[n].c << " drop Order=" << dr.o << "\n";
                fails++;
            }
        }
    };
    auto needed = [&]() {                      // scan bound for Orders done+1..N
        u64 m = 0;
        for (int n = done + 1; n <= N; n++) m = std::max(m, win[n]);
        return m;
    };
    auto save_state = [&]() {
        std::string   tmp = progf + ".state.tmp";
        std::ofstream f(tmp);
        f << W << " " << N << " " << A << " " << ROUND << "\n";
        for (int n = 1; n <= maxo; n++)
            if (best[n].c) f << n << " " << best[n].c << " " << best[n].d << "\n";
        f.close();
        std::rename(tmp.c_str(), (progf + ".state").c_str());
    };
    flush();
    std::cerr << "from the wheel: Orders 1.." << done << "\n";
    plog("started N=" + std::to_string(N) + " W=" + std::to_string(W) + " threads=" + std::to_string(NT) +
         ", wheel Orders 1.." + std::to_string(wheel_top) + ", needed x0 < " + std::to_string(needed()));

    using clock   = std::chrono::steady_clock;
    const auto t0 = clock::now();
    auto secs     = [](clock::duration d) { return std::chrono::duration<double>(d).count(); };
    auto last_log = t0;
    const u64  X0 = A << W;                     // scan bound at this start (resume)
    const bool tty = isatty(2);
    while (done < N) {
        int done0 = done;
        const auto tr = clock::now();
        std::vector<std::vector<Best>> lb(NT, best);
        std::vector<std::vector<u64>>  lf(NT, std::vector<u64>(maxo + 1, NONE));
        std::vector<std::thread>       th;
        for (int k = 0; k < NT; k++) {
            th.emplace_back([&, k]() {
                auto &b = lb[k];
                auto &f = lf[k];
                for (u64 a = A; a < A + ROUND; a++) {
                    for (size_t i = k; i < surv.size(); i += NT) {
                        const Surv &s  = surv[i];
                        u64         x0 = (a << W) + s.r;
                        Drop        dr = drop_of(x0, a, s, W);
                        if (dr.o > maxo) continue;
                        if (x0 < f[dr.o]) f[dr.o] = x0;
                        if (better(dr.d, x0, b[dr.o])) b[dr.o] = {x0, dr.d};
                    }
                }
            });
        }
        for (auto &t : th) t.join();
        for (int n = 0; n <= maxo; n++) {
            bool ch = false;
            for (int k = 0; k < NT; k++) {
                first_id[n] = std::min(first_id[n], lf[k][n]);
                if (better(lb[k][n].d, lb[k][n].c, best[n]) && lb[k][n].c) { best[n] = lb[k][n]; ch = true; }
            }
            if (ch && n >= 1 && n <= N) win[n] = window(n, best[n]);
        }
        A += ROUND;
        flush();
        u64    X  = A << W, need = done < N ? needed() : X;
        double dt = secs(clock::now() - tr), el = secs(clock::now() - t0);
        u64    rate = (u64)((X - X0) / std::max(el, 1e-3));          // x0 per second
        u64    eta  = need > X && rate ? (need - X) / rate : 0;      // at most: windows only shrink
        std::ostringstream ln;
        ln << "elapsed " << hms(el) << "  x0 < " << X << " of needed " << need << " (per mille "
           << (need ? (u64)((u128)X * 1000 / need) : 1000) << ", ETA at most " << hms((double)eta)
           << ")  Orders final 1.." << done << " of " << N << "  " << rate << " x0/s  slow "
           << slow_count.load();
        if (tty) std::cerr << "\r\033[K" << ln.str().substr(0, 160) << std::flush;
        else std::cerr << ln.str() << std::endl;
        if (done > done0 || secs(clock::now() - last_log) >= 600 || done == N) {
            plog(ln.str());
            save_state();
            last_log = clock::now();
        }
        u64 next = std::max<u64>(1, A / 4);
        if (dt > 60) next = std::min(next, std::max<u64>(1, (u64)(ROUND * 60 / dt)));
        if (need > X) next = std::min(next, ((need - X) >> W) + 1);   // no scan past the bound
        ROUND = next;
    }

    if (tty) std::cerr << "\n";
    // check: the first x0 met per Order is the A122442 start value (a resumed run skips this)
    int mism = 0, nchk = 0;
    if (resf.empty())
        for (int n = 1; n <= maxo; n++)
            if (seed[n] && first_id[n] != NONE && first_id[n] <= (A << W)) {
                nchk++;
                if (first_id[n] != seed[n]) {
                    mism++;
                    std::cerr << "MISMATCH n=" << n << " first x0 " << first_id[n] << " seed " << seed[n] << "\n";
                }
            }
    fails += mism;
    if (width_fail.load()) fails++;
    std::ostringstream check;
    check << "check: " << (fails ? "FAILED" : "every best drops at its own Order with its own drop value")
          << "; first x0 per Order = A122442: " << nchk - mism << " of " << nchk
          << "; prefixes with 3^j < 2^l and no drop: " << width_fail.load();
    std::cerr << check.str() << "\n";
    double wall = std::chrono::duration<double>(std::chrono::steady_clock::now() - t_start).count();
    std::cout << "# finished: " << utc_now() << ", wall time " << hms(wall) << " (" << (long)(wall + 0.5)
              << " s)\n# scanned: x0 < " << (A << W) << ", slow path " << slow_count.load()
              << "\n# " << check.str() << "\n# n c T^L(c) window\n";
    for (int n = 1; n <= N; n++)
        std::cout << "# " << n << " " << best[n].c << " " << best[n].d << " " << win[n] << "\n";
    std::cout << std::flush;
    plog(std::string(fails ? "FAILED " : "DONE ") + check.str());
    return fails ? 2 : 0;
}
