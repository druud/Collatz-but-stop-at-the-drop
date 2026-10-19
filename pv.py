#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Virtual cache of admissible parity vectors (PVs) under the map T.

A PV of Order p3 is a 0/1 sequence of length p2(p3) whose every proper nonempty
prefix has product (3/2)^ones (1/2)^zeros > 1 and whose full product is < 1.

Representation: an int v with bit j = parity of step j (LSB first). The length
p2(popcount(v)) is implied, so the trailing zeros of the PV are the implied
high zero bits of v; the Order-0 PV [0] is v = 0.
Key: the odd part (A000265) of the PV read as a binary number: the PV as a
'0'/'1' string in step order with trailing zeros removed ('0' for v = 0). All
attributes are computed from it.

Command line (python3 pv.py -h, or python3 pv.py CMD -h):
  python3 pv.py                    help and a short demo
  python3 pv.py attrs KEY ...      attributes of each odd part
  python3 pv.py list O [N] [--tsv] first N (default 50) PVs of Order O
  python3 pv.py xs O [N]           x and odd part of the first N (default 50) PVs,
                                   tab-separated (sort -n works)
  python3 pv.py count O ...        number of PVs of each Order (A100982)
  python3 pv.py rank KEY           1-based rank within its Order
  python3 pv.py unrank O R         PV of Order O with rank R
  python3 pv.py pack KEY           packed forms as hex
  python3 pv.py excess O [N]       excess r, gap g, q = r/g and accumulated excess s
                                   of the first N PVs
  python3 pv.py maxq O ...         PV with the largest q of each Order
  python3 pv.py records N          upper and lower record Orders up to N, with p2 and
                                   the block factor f = 3^O / 2^p2
  python3 pv.py first O            first PV of Order O and its chain of first PVs
  python3 pv.py sweep KEY          sweep, start sweep and cut sweep of an odd part
  python3 pv.py smooth N ...       the N-th 3-smooth number 2^j 3^i (A003586)
  python3 pv.py brackets KEY       bracket word of an odd part
  python3 pv.py walk KEY           running excess per odd step, against the gap
  python3 pv.py test               run the self-test

Library:
  import pv
  pv.attrs('1101')        Attrs(key='1101', p2=5, p3=3, x=11, drop=10, ...)
  pv.key(pv.unrank(7, 18))   '111101011'
  pv.chain_code(v)        [(6, 4), (0, 1)]
  pv.pack_pv_fixed(v) / pv.unpack_pv_fixed(buf)
  pv.excess_row(v)        Excess(key=..., x=..., r=..., g=..., q=..., s=...)
  pv.upper_records(41)    [1, 3, 5, 17, 29, 41]
  pv.key(pv.sweep(pv.from_key('110111')))    '111011'
  pv.bracket_word(pv.from_key('1101101'))    [0, 1, 0, 1, 3]
  pv.smooth(51)           (5, 4): the 51st 3-smooth number is 2^5 3^4

Tests: python3 pv.py test
"""
from fractions import Fraction
from functools import lru_cache, reduce
from itertools import accumulate, count as naturals, islice, repeat, takewhile
from operator import gt, lt, or_
from typing import NamedTuple


def logint(n, b):
    """Largest k with b^k <= n, for n >= 1 and b >= 2, in integers only (as PARI
    logint). Base 2: the bit length. Otherwise the squares b^(2^i) <= n, then the
    bits of k from the top down: a square is taken when the product stays <= n."""
    if b == 2:
        return n.bit_length() - 1
    squares = list(takewhile(lambda q: q <= n, accumulate(repeat(b), lambda q, _: q * q)))
    if not squares:
        return 0

    def take(state, i):
        k, q = state
        r = q * squares[i]
        return (k | 1 << i, r) if r <= n else state

    top = len(squares) - 1
    return reduce(take, range(top - 1, -1, -1), (1 << top, squares[top]))[0]


@lru_cache(maxsize=None)
def p2(o):
    """Length of an admissible PV of Order o: the number of binary digits of 3^o."""
    return logint(3 ** o, 2) + 1


def T(x):
    return (3 * x + 1) // 2 if x & 1 else x // 2


# --- representation ---------------------------------------------------------

# int.bit_count from Python 3.10, else counting '1' digits.
_popcount = getattr(int, 'bit_count', lambda v: bin(v).count('1'))


def order(v):
    return _popcount(v)


def length(v):
    return p2(order(v))


def key(v):
    """Core string in step order: the bits of v from bit 0 up."""
    return format(v, 'b')[::-1]


def from_key(k):
    return int(k[::-1], 2)


def bits(v):
    """The PV as a 0/1 list of length p2."""
    return [v >> j & 1 for j in range(length(v))]


def is_admissible(v):
    """Every proper prefix of length m has at least _min_ones(m) ones; the whole
    product 3^p3 / 2^p2 < 1 holds by the implied length."""
    n = length(v)
    ones = accumulate(v >> j & 1 for j in range(n - 1))
    return not v >> n and all(k >= _min_ones(m) for m, k in enumerate(ones, 1))


# --- drop formula, class id, drop -------------------------------------------

def rho(v):
    """rho in T^p2(x) = (3^p3 x + rho) / 2^p2 for every x with parity bits v."""
    return reduce(lambda r, j: 3 * r + (1 << j),
                  (j for j in range(length(v)) if v >> j & 1), 0)


def d_23(v):
    """2^p2 - 3^p3 > 0."""
    return (1 << length(v)) - 3 ** order(v)


def class_id(v):
    """Least positive x whose first p2 T-parity bits are v."""
    L = length(v)
    x = -rho(v) * pow(3, -order(v), 1 << L) % (1 << L)
    return x if x > 0 else 1 << L


def drop(v):
    return (3 ** order(v) * class_id(v) + rho(v)) >> length(v)


# --- chain ------------------------------------------------------------------

def chain(v):
    """Blocks after the leading 1: admissible PVs of Order >= 1, then 0 (the PV
    [0]) if a tail 0 is present. The Order-0 PV has the empty chain.
    With W(t) = 3^(ones in the first t bits after the leading 1) * 2^(L-1-t),
    the level scaled to integers, a block ends at every new record low of W."""
    if v == 0:
        return []
    L = length(v)
    ones = accumulate((v >> j & 1 for j in range(1, L)), initial=0)
    W = [3 ** k << (L - 1 - t) for t, k in enumerate(ones)]
    lows = list(accumulate(W, min))
    ends = [t for t in range(1, L) if W[t] < lows[t - 1]]
    return [v >> (1 + a) & ((1 << (b - a)) - 1) for a, b in zip([0] + ends, ends)]


def from_chain(blocks):
    """1 :: blocks; each block contributes its implied length."""
    offsets = accumulate((length(blk) for blk in blocks), initial=1)
    return reduce(or_, (blk << off for blk, off in zip(blocks, offsets)), 1)


def rho_from_chain(blocks):
    """rho of 1 :: blocks, composed from the blocks' own rho values."""
    offsets = accumulate((length(blk) for blk in blocks), initial=1)
    return reduce(lambda r, bo: 3 ** order(bo[0]) * r + (rho(bo[0]) << bo[1]),
                  zip(blocks, offsets), 1)


# --- rank / unrank (1-based, sorted with 0 < 1 in step order) ---------------

@lru_cache(maxsize=None)
def _min_ones(m):
    """Least j with 3^j > 2^m, the number of base-3 digits of 2^m (dual of p2):
    a prefix of length m needs at least j ones."""
    return logint(2 ** m, 3) + 1


def _allowed(o, ones, zeros, bit):
    """Whether appending `bit` keeps a valid prefix on course to Order o."""
    L, m = p2(o), ones + zeros
    j = ones + bit
    if j > o:
        return False
    if m + 1 < L:
        return j >= _min_ones(m + 1)
    return True


@lru_cache(maxsize=None)
def _completion_table(o):
    """t[m][j]: completions of a valid prefix of length m with j ones; only the
    band of prefixes that stay above the line and can still finish is filled."""
    L = p2(o)

    def row(nxt, m):
        # appending a bit is allowed when the new prefix keeps >= need ones
        need = _min_ones(m + 1) if m + 1 < L else 0
        lo = max(0, m - (L - o), o - (L - m), _min_ones(m) if m > 0 else 0)
        hi = min(o, m)
        band = [(nxt[j] if j >= need else 0) + (nxt[j + 1] if need <= j + 1 <= o else 0)
                for j in range(lo, hi + 1)]
        return [0] * lo + band + [0] * (o - max(hi, lo - 1))

    last = [0] * o + [1]
    return list(accumulate(range(L - 1, -1, -1), row, initial=last))[::-1]


def completions(o, ones, zeros):
    """Number of admissible PVs of Order o extending a valid prefix with the
    given counts of ones and zeros."""
    return _completion_table(o)[ones + zeros][ones]


def count(o):
    """|A100982(o)|: number of admissible PVs of Order o."""
    return 1 if o == 0 else completions(o, 1, 0)


def rank(v):
    """1-based position among the admissible PVs of the same Order."""
    o = order(v)
    if o == 0:
        return 1
    ones = list(accumulate((v >> j & 1 for j in range(length(v))), initial=0))
    return 1 + sum(completions(o, ones[m], m - ones[m] + 1)
                   for m in range(1, length(v))
                   if v >> m & 1 and _allowed(o, ones[m], m - ones[m], 0))


def unrank(o, r):
    """Admissible PV of Order o with 1-based rank r."""
    if o == 0:
        return 0

    def step(state, m):
        v, ones, r = state
        c = completions(o, ones, m - ones + 1) if _allowed(o, ones, m - ones, 0) else 0
        return (v, ones, r) if r <= c else (v | 1 << m, ones + 1, r - c)

    return reduce(step, range(1, p2(o)), (1, 1, r))[0]


# --- (d, c) encoding: chain as (Order, rank) pairs --------------------------

def chain_code(v):
    """[(o_i, rank_i), ...] for the chain blocks; the tail 0 is (0, 1)."""
    return [(order(blk), rank(blk)) for blk in chain(v)]


def from_chain_code(code):
    if not code:
        return 0
    return from_chain([unrank(o, r) for o, r in code])


# --- excess vs gap ----------------------------------------------------------
# T^k(x) = c_k x + e_k, c_k = 3^(ones in the first k bits) / 2^k.
# Excess r = e/(c x) = rho/(3^p3 x) = (1/(3x)) sum over odd steps j of 1/c_j.
# Gap g = 1/c - 1 = d_23/3^p3. Drop iff r < g, i.e. q = r/g < 1.
# Accumulated excess s = sum over odd steps j of 1/c_j = rho/3^(p3-1) = 3 x r.

def odd_steps(v):
    return [j for j in range(length(v)) if v >> j & 1]


def excess_terms(v):
    """1/c_j = 2^j / 3^(ones before step j) for each odd step j."""
    return [Fraction(1 << j, 3 ** i) for i, j in enumerate(odd_steps(v))]


def excess_sum(v):
    """s = sum of 1/c_j over the odd steps; the same for every member of the class."""
    return sum(excess_terms(v), Fraction(0))


def excess(v, x):
    return excess_sum(v) / (3 * x)


def gap(v):
    return Fraction(d_23(v), 3 ** order(v))


def excess_ratio(v, x):
    """q = r/g = rho / (d_23 x)."""
    return Fraction(rho(v), d_23(v) * x)


class Excess(NamedTuple):
    key: str
    x: int
    r: Fraction
    g: Fraction
    q: Fraction
    s: Fraction


def least_x(v):
    """Least x > 1 with parity bits v: the class id, or the next member for x = 1."""
    x = class_id(v)
    return x if x > 1 else x + (1 << length(v))


def excess_row(v):
    x = least_x(v)
    return Excess(key(v), x, excess(v, x), gap(v), excess_ratio(v, x), excess_sum(v))


class WalkStep(NamedTuple):
    j: int              # odd step
    inv_c: Fraction     # 1/c_j
    r: Fraction         # excess after step j
    share: Fraction     # r / g


def walk(v):
    """Running excess over the odd steps of v at least_x(v)."""
    x, g, terms = least_x(v), gap(v), excess_terms(v)
    return [WalkStep(j, t, s / (3 * x), s / (3 * x) / g)
            for j, t, s in zip(odd_steps(v), terms, accumulate(terms))]


# --- record Orders, block factor, first PVs ----------------------------------
# Block factor f(o) = 3^o / 2^p2(o), between 1/2 and 1. Upper record Orders: f closer
# to 1 than at every earlier Order, that is p2(o)/o below every earlier one. Lower
# record Orders: f closer to 1/2, that is (p2(o) - 1)/o above every earlier one.

def block_factor(o):
    """f(o) = 3^o / 2^p2(o): the level change across a block of Order o."""
    return Fraction(3 ** o, 1 << p2(o))


def _records(ratio, better, n):
    """Orders 1..n whose ratio is `better` than that of every earlier Order."""
    vals = [ratio(o) for o in range(1, n + 1)]
    best = accumulate(vals, lambda m, r: r if better(r, m) else m)
    return [o for o, r, m in zip(naturals(1), vals, [None] + list(best))
            if m is None or better(r, m)]


def upper_records(n):
    """Upper record Orders up to n: 1, 3, 5, 17, 29, 41, 94, ..."""
    return _records(lambda o: Fraction(p2(o), o), lt, n)


def lower_records(n):
    """Lower record Orders up to n: 1, 2, 7, 12, 53, 359, ..."""
    return _records(lambda o: Fraction(p2(o) - 1, o), gt, n)


class Record(NamedTuple):
    order: int
    kind: str           # 'upper', 'lower' or 'both'
    p2: int


RECORD_KIND = {(True, True): 'both', (True, False): 'upper', (False, True): 'lower'}


def records(n):
    """The record Orders of either kind up to n."""
    up, low = set(upper_records(n)), set(lower_records(n))
    return [Record(o, RECORD_KIND[o in up, o in low], p2(o)) for o in sorted(up | low)]


@lru_cache(maxsize=None)
def _records_band(k):
    """The lower and the upper record Orders up to 2^k, computed once per k."""
    return tuple(lower_records(1 << k)), tuple(upper_records(1 << k))


def last_records(n):
    """(a, b): the last lower and the last upper record Order below n (1, 1 if none)."""
    low, up = _records_band(max(n - 1, 1).bit_length())
    return (max((o for o in low if o < n), default=1),
            max((o for o in up if o < n), default=1))


class FirstBlock(NamedTuple):
    odd: int            # odd steps up to the end of this block
    order: int
    key: str


def first_chain(o):
    """The blocks of the first PV of Order o, after its leading 1: first PVs again,
    cut at the lower record Orders."""
    blocks = chain(unrank(o, 1))
    odd = accumulate((order(blk) for blk in blocks), initial=1)
    return [FirstBlock(k, order(blk), key(blk)) for k, blk in zip(islice(odd, 1, None), blocks)]


# --- levels, sweeps, brackets ---------------------------------------------------

def levels(v):
    """W[j] = 3^(ones in the first j bits) * 2^(L - j) for j = 0..L: the level after
    j steps, scaled by 2^L to an integer (a 3-smooth number)."""
    L = length(v)
    ones = accumulate((v >> j & 1 for j in range(L)), initial=0)
    return [3 ** k << (L - j) for j, k in enumerate(ones)]


def _steps_in_order(v, idx):
    """The bits of v read in the order idx: bit t of the result is bit idx[t] of v."""
    return reduce(or_, ((v >> i & 1) << t for t, i in enumerate(idx)), 0)


def sweep(v):
    """The steps sorted by the level at which they end, highest first."""
    W = levels(v)
    return _steps_in_order(v, sorted(range(length(v)), key=lambda i: -W[i + 1]))


def start_sweep(v):
    """The steps sorted by the level at which they start, lowest first."""
    W = levels(v)
    return _steps_in_order(v, sorted(range(length(v)), key=lambda i: W[i]))


def cut_sweep(v):
    """The start sweep of the steps before the final halving; that halving stays last."""
    W = levels(v)
    return _steps_in_order(v, sorted(range(length(v) - 1), key=lambda i: W[i]))


def bracket_word(v):
    """A bracket opens at every odd step and closes where the level first falls below
    the level at which it opened. Per odd step: the brackets that close after it and
    not after the next odd step."""
    W, L, odd = levels(v), length(v), odd_steps(v)
    closes = [next(j for j in range(i + 1, L + 1) if W[j] < W[i]) for i in odd]
    return [sum(1 for c in closes if k < c <= nxt) for k, nxt in zip(odd, odd[1:] + [L])]


# --- 3-smooth numbers (A003586) --------------------------------------------------
# 2^j 3^i has j + p2(i) binary digits, so those of B digits are 2^(B - p2(i)) 3^i for
# the Orders i < u(B). With a, b the last lower and upper record Orders below u(B)
# they rise along i = k a mod (a + b), k = 0, 1, ...

def powers_of_3_below(k):
    """u(k): the number of powers of 3 below 2^k."""
    return _min_ones(k) if k else 0


def smooth_rank(j, i):
    """1-based place of 2^j 3^i among the 3-smooth numbers (Mintz 1981)."""
    return (1 + i * j + sum(p2(k) for k in range(1, i + 1))
            + sum(powers_of_3_below(k) for k in range(1, j + 1)))


def smooth(n):
    """(j, i) with 2^j 3^i the n-th 3-smooth number, n >= 1."""
    upto = accumulate(powers_of_3_below(B) for B in naturals(1))
    B, below = next((B, s - powers_of_3_below(B)) for B, s in zip(naturals(1), upto) if n <= s)
    N = powers_of_3_below(B)
    a, b = last_records(N)
    in_class = (i for i in (k * a % (a + b) for k in range(a + b)) if i < N)
    i = next(islice(in_class, n - below - 1, None))
    return B - p2(i), i


class Smooth(NamedTuple):
    n: int
    j: int              # exponent of 2
    i: int              # exponent of 3
    digits: int         # binary digits of 2^j 3^i


def smooth_row(n):
    j, i = smooth(n)
    return Smooth(n, j, i, j + p2(i))


# --- all attributes ---------------------------------------------------------

class Attrs(NamedTuple):
    key: str
    p2: int
    p3: int
    x: int
    drop: int
    rank: int
    rho: int
    chain: list     # block keys
    code: list      # (Order, rank) per block


def attrs(k):
    v = from_key(k)
    return Attrs(k, length(v), order(v), class_id(v), drop(v), rank(v), rho(v),
                 [key(blk) for blk in chain(v)], chain_code(v))


# --- packed storage (BER compressed integers, as Perl pack 'w') -------------

def BER_encode(n):
    """Big-endian base-128 digits; bit 7 set on all but the last byte."""
    digits = [n >> 7 * i & 0x7F for i in range(max(1, (n.bit_length() + 6) // 7))]
    return bytes(d | 0x80 if i else d for i, d in enumerate(digits))[::-1]


def BER_decode(buf, pos=0):
    """Returns (n, next position)."""
    end = next(i for i in naturals(pos) if not buf[i] & 0x80)
    return reduce(lambda n, byte: n << 7 | byte & 0x7F, buf[pos:end + 1], 0), end + 1


def _BER_decode_n(buf, pos, k):
    """k BER integers from pos: (list, next position)."""
    return reduce(lambda acc, _: (lambda n, p: (acc[0] + [n], p))(*BER_decode(buf, acc[1])),
                  range(k), ([], pos))


def pack_pv(v):
    """p3 and rank - 1 as two BER integers."""
    return BER_encode(order(v)) + BER_encode(rank(v) - 1)


def unpack_pv(buf, pos=0):
    (o, r), pos_next = _BER_decode_n(buf, pos, 2)
    return unrank(o, r + 1), pos_next


def pack_chain(v):
    """Number of blocks, then (o_i, rank_i - 1) per block, all BER."""
    code = chain_code(v)
    return BER_encode(len(code)) + b''.join(BER_encode(o) + BER_encode(r - 1)
                                            for o, r in code)


def unpack_chain(buf, pos=0):
    k, pos_k = BER_decode(buf, pos)
    nums, pos_next = _BER_decode_n(buf, pos_k, 2 * k)
    return from_chain_code(list(zip(nums[0::2], (r + 1 for r in nums[1::2])))), pos_next


def pack_many(pvs, packer=pack_pv):
    return b''.join(packer(v) for v in pvs)


def unpack_many(blob, unpacker=unpack_pv):
    """Unpack consecutive PVs until the blob is used up."""
    steps = accumulate(repeat(None),
                       lambda acc, _: unpacker(blob, acc[1]) if acc[1] < len(blob) else None,
                       initial=(None, 0))
    return [v for v, _ in takewhile(lambda st: st is not None, islice(steps, 1, None))]


def pack_pv_fixed(v):
    """BER p3, then rank - 1 in the fixed byte width that count(p3) needs."""
    o = order(v)
    width = ((count(o) - 1).bit_length() + 7) // 8
    return BER_encode(o) + (rank(v) - 1).to_bytes(width, 'big')


def unpack_pv_fixed(buf, pos=0):
    o, pos = BER_decode(buf, pos)
    width = ((count(o) - 1).bit_length() + 7) // 8
    r = int.from_bytes(buf[pos:pos + width], 'big')
    return unrank(o, r + 1), pos + width


# --- self-test --------------------------------------------------------------

def _enumerate_order(o):
    return [unrank(o, r) for r in range(1, count(o) + 1)]


_A100982 = [1, 1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652, 8045]  # Orders 0..13


def _test_logint():
    for b in (2, 3, 5, 10):
        for k in list(range(40)) + [100, 1000]:
            assert logint(b ** k, b) == k
            assert logint(b ** (k + 1) - 1, b) == k
        assert all(b ** logint(n, b) <= n < b ** (logint(n, b) + 1) for n in range(1, 2000))


def _test_counts():
    assert [count(o) for o in range(14)] == _A100982


def _test_rank_unrank_sorted():
    for o in range(0, 12):
        pvs = _enumerate_order(o)
        assert all(is_admissible(v) for v in pvs)
        seqs = [bits(v) for v in pvs]
        assert seqs == sorted(seqs)
        assert [rank(v) for v in pvs] == list(range(1, len(pvs) + 1))


def _test_key_roundtrip():
    for o in range(0, 12):
        for v in _enumerate_order(o):
            assert from_key(key(v)) == v
            assert bits(v)[:len(key(v))] == [int(c) for c in key(v)]


def _test_class_id_and_drop():
    for o in range(0, 11):
        for v in _enumerate_order(o):
            x, L = class_id(v), length(v)
            assert 0 < x <= 2 ** L
            y, seq = x, []
            for _ in range(L):
                seq.append(y & 1)
                y = T(y)
            assert seq == bits(v) and y == drop(v)
            assert 3 ** o * x + rho(v) == drop(v) * 2 ** L


def _test_chain():
    for o in range(1, 12):
        for v in _enumerate_order(o):
            blocks = chain(v)
            assert from_chain(blocks) == v
            assert all(is_admissible(blk) for blk in blocks)
            assert all(order(blk) >= 1 for blk in blocks[:-1])
            assert rho_from_chain(blocks) == rho(v)
            assert from_chain_code(chain_code(v)) == v


def _test_excess():
    for o in range(0, 11):
        for v in _enumerate_order(o):
            x, e = least_x(v), excess_row(v)
            y = reduce(lambda y, _: T(y), range(length(v)), x)
            assert e.r == Fraction(rho(v), 3 ** o * x)
            assert e.q == e.r / e.g
            assert e.s == 3 * x * e.r == Fraction(rho(v), 3 ** max(o - 1, 0))
            assert (e.q < 1) == (y < x)
            steps = walk(v)
            assert [s.r for s in steps] == sorted(s.r for s in steps)
            assert not steps or steps[-1].share == e.q


def _test_BER():
    for n in list(range(300)) + [2 ** 64 - 1, 3 ** 200]:
        buf = BER_encode(n)
        assert BER_decode(buf) == (n, len(buf))
    assert BER_encode(300).hex() == '822c'


def _test_pack():
    pvs = [v for o in range(0, 10) for v in _enumerate_order(o)]
    for packer, unpacker in ((pack_pv, unpack_pv), (pack_chain, unpack_chain),
                             (pack_pv_fixed, unpack_pv_fixed)):
        for v in pvs:
            buf = packer(v)
            assert unpacker(buf) == (v, len(buf))
        assert unpack_many(pack_many(pvs, packer), unpacker) == pvs


def _test_records():
    assert upper_records(310) == [1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306]
    assert lower_records(400) == [1, 2, 7, 12, 53, 359]
    by_factor = lambda better: [o for o in range(1, 80)
                                if all(better(block_factor(o), block_factor(a))
                                       for a in range(1, o))]
    assert by_factor(gt) == upper_records(79) and by_factor(lt) == lower_records(79)
    assert [r.kind for r in records(7)] == ['both', 'lower', 'upper', 'upper', 'lower']
    assert last_records(2) == (1, 1) and last_records(13) == (12, 5)


def _greedy_first(o):
    """Every halving that keeps the level above 1, until the last of o odd steps."""
    def step(state, j):
        v, num, ones = state                    # level = num / 2^j
        halve = ones == o or num > 1 << (j + 1)
        return (v, num, ones) if halve else (v | 1 << j, 3 * num, ones + 1)
    return reduce(step, range(p2(o)), (0, 1, 0))[0]


def _test_first():
    for o in range(1, 60):
        v, blocks = unrank(o, 1), first_chain(o)
        assert v == _greedy_first(o)
        assert all(unrank(blk.order, 1) == from_key(blk.key) for blk in blocks)
        cuts = [blk.odd for blk in blocks if blk.order]
        assert cuts == sorted((set(lower_records(o)) | {o}) - {1})
    assert [blk.order for blk in first_chain(53) if blk.order] == [1, 5, 5, 41]


def _test_sweeps():
    for o in range(1, 10):
        pvs = _enumerate_order(o)
        assert all(is_admissible(sweep(v)) and is_admissible(cut_sweep(v)) for v in pvs)
        assert len(set(map(sweep, pvs))) == len(pvs) == len(set(map(start_sweep, pvs)))
        assert all(is_admissible(start_sweep(v)) for v in pvs) == (o in upper_records(o))
        assert (len(set(map(cut_sweep, pvs))) == len(pvs)) == (o in lower_records(o))
    assert [key(f(from_key('110111'))) for f in (sweep, start_sweep, cut_sweep)] == [
        '111011', '1111001', '111101']


def _test_brackets():
    assert bracket_word(from_key('1101101')) == [0, 1, 0, 1, 3]
    for o in range(1, 11):
        pvs = _enumerate_order(o)
        words = [bracket_word(v) for v in pvs]
        assert all(sum(w) == o for w in words)
        assert len(set(map(tuple, words))) == len(pvs)
        for v, w in zip(pvs, words):
            inner = sum((bracket_word(blk) for blk in chain(v)), [0])
            assert w == inner[:-1] + [inner[-1] + 1]


def _test_smooth():
    listed = sorted(2 ** j * 3 ** i for j in range(80) for i in range(51))[:2000]
    assert listed[-1] < 2 ** 79
    assert [2 ** j * 3 ** i for j, i in map(smooth, range(1, 2001))] == listed
    assert smooth(51) == (5, 4) and smooth_row(51).digits == 12
    assert all(smooth(smooth_rank(j, i)) == (j, i) for j in range(40) for i in range(25))


TESTS = (('logint', _test_logint),
         ('counts', _test_counts),
         ('rank_unrank_sorted', _test_rank_unrank_sorted),
         ('key_roundtrip', _test_key_roundtrip),
         ('class_id_and_drop', _test_class_id_and_drop),
         ('chain', _test_chain),
         ('excess', _test_excess),
         ('BER', _test_BER),
         ('pack', _test_pack),
         ('records', _test_records),
         ('first', _test_first),
         ('sweeps', _test_sweeps),
         ('brackets', _test_brackets),
         ('smooth', _test_smooth))


def run_tests():
    """Run every test; yield its name once it passed."""
    for name, test in TESTS:
        test()
        yield (name,)


# --- command line -----------------------------------------------------------

# Attrs fields by position: 0 key, 1 p2, 2 p3, 3 x, 4 drop, 5 rank, 6 rho, 7 chain, 8 code
ROW = '{0:>12}  p2={1:<3} p3={2:<3} rank={5:<4} x={3:<8} drop={4:<8} rho={6:<8} code={8}'
TSV = '\t'.join('{%d}' % i for i in range(len(Attrs._fields)))
TSV_HEADER = '\t'.join(Attrs._fields)
# Excess fields: 0 key, 1 x, 2 r, 3 g, 4 q, 5 s; WalkStep fields: 0 j, 1 inv_c, 2 r, 3 share
EXCESS_ROW = 'x={1:<8} q={4}  r={2}  g={3}  s={5}  {0}'
MAXQ_ROW = '{0:<4} x={2:<8} q={5}  r={3}  g={4}  s={6}  {1}'
WALK_ROW = '{0:>4}  1/c={1}  r={2}  r/g={3}'
PACKERS = (('pv', pack_pv), ('pv_fixed', pack_pv_fixed), ('chain', pack_chain))
# Record fields: 0 order, 1 kind, 2 p2; FirstBlock fields: 0 odd, 1 order, 2 key
RECORD_ROW = '{0:>6}  {1:<5}  p2={2:<6} f=3^{0}/2^{2}'
FIRST_ROW = '{0:>6}  {1:>6}  {2}'
FIRST_HEADER = '{0}\n   odd   Order  key'
# Smooth fields: 0 n, 1 j, 2 i, 3 digits
SMOOTH_ROW = '{0}  2^{1} 3^{2}  digits={3}'
SWEEPS = (('sweep', sweep), ('start', start_sweep), ('cut', cut_sweep))
ADMISSIBLE = {True: 'admissible', False: 'not admissible'}


class Command(NamedTuple):
    help: str
    args: list          # (argument, argparse options) pairs
    fmt: object         # format string, or function of the parsed arguments
    rows: object        # function: parsed arguments -> iterable of tuples
    header: object = None


def _each_rank(o, n):
    return (unrank(o, r) for r in range(1, min(n, count(o)) + 1))


ORDER = dict(type=int, metavar='O')
FIRST_N = dict(type=int, nargs='?', default=50, metavar='N')

COMMANDS = {
    'attrs':  Command('attributes of each core key',
                      [('keys', dict(nargs='+', metavar='KEY'))],
                      '{0}',
                      lambda a: ((attrs(k),) for k in a.keys)),
    'list':   Command('first N (default 50) PVs of Order O',
                      [('o', ORDER), ('n', FIRST_N),
                       ('--tsv', dict(action='store_true', help='tab-separated with header'))],
                      lambda a: TSV if a.tsv else ROW,
                      lambda a: (attrs(key(v)) for v in _each_rank(a.o, a.n)),
                      lambda a: TSV_HEADER if a.tsv else None),
    'xs':     Command('x and key of the first N PVs of Order O, tab-separated',
                      [('o', ORDER), ('n', FIRST_N)],
                      '{0}\t{1}',
                      lambda a: ((class_id(v), key(v)) for v in _each_rank(a.o, a.n))),
    'count':  Command('number of PVs of each Order (A100982)',
                      [('orders', dict(type=int, nargs='+', metavar='O'))],
                      '{0} {1}',
                      lambda a: ((o, count(o)) for o in a.orders)),
    'rank':   Command('1-based rank of a key within its Order',
                      [('key', {})],
                      '{0}',
                      lambda a: [(rank(from_key(a.key)),)]),
    'unrank': Command('PV of Order O with rank R',
                      [('o', ORDER), ('r', dict(type=int, metavar='R'))],
                      '{0} {1}',
                      lambda a: ((key(v), bits(v)) for v in [unrank(a.o, a.r)])),
    'pack':   Command('packed forms of a key as hex',
                      [('key', {})],
                      '{0:<8} {1}',
                      lambda a: ((name, packer(from_key(a.key)).hex())
                                 for name, packer in PACKERS)),
    'excess': Command('excess r, gap g, q = r/g of the first N PVs of Order O',
                      [('o', ORDER), ('n', FIRST_N)],
                      EXCESS_ROW,
                      lambda a: (excess_row(v) for v in _each_rank(a.o, a.n))),
    'maxq':   Command('PV with the largest q of each Order',
                      [('orders', dict(type=int, nargs='+', metavar='O'))],
                      MAXQ_ROW,
                      lambda a: ((o, *max((excess_row(v) for v in _each_rank(o, count(o))),
                                          key=lambda e: e.q))
                                 for o in a.orders)),
    'records': Command('upper and lower record Orders up to N, with p2 and block factor',
                       [('n', dict(type=int, metavar='N'))],
                       RECORD_ROW,
                       lambda a: records(a.n)),
    'first':  Command('first PV of Order O and its chain of first PVs',
                      [('o', ORDER)],
                      FIRST_ROW,
                      lambda a: first_chain(a.o),
                      lambda a: FIRST_HEADER.format(key(unrank(a.o, 1)))),
    'sweep':  Command('sweep, start sweep and cut sweep of a key',
                      [('key', {})],
                      '{0:<6} {1}  {2}',
                      lambda a: ((name, key(w), ADMISSIBLE[is_admissible(w)])
                                 for name, w in ((name, f(from_key(a.key)))
                                                 for name, f in SWEEPS))),
    'smooth': Command('the N-th 3-smooth number 2^j 3^i (A003586)',
                      [('ns', dict(type=int, nargs='+', metavar='N'))],
                      SMOOTH_ROW,
                      lambda a: (smooth_row(n) for n in a.ns)),
    'brackets': Command('bracket word of a key',
                        [('key', {})],
                        '{0}',
                        lambda a: [(bracket_word(from_key(a.key)),)]),
    'test':   Command('run the self-test',
                      [],
                      'ok {0}',
                      lambda a: run_tests()),
    'walk':   Command('running excess per odd step of a key, against the gap',
                      [('key', {})],
                      WALK_ROW,
                      lambda a: walk(from_key(a.key))),
}


def _run(args, cmd):
    """Print the optional header, then the format filled from every row."""
    fmt = cmd.fmt(args) if callable(cmd.fmt) else cmd.fmt
    header = cmd.header(args) if callable(cmd.header) else cmd.header
    if header:
        print(header)
    for row in cmd.rows(args):
        print(fmt.format(*row))


def _parser():
    import argparse
    ap = argparse.ArgumentParser(prog='pv.py', description='Virtual cache of admissible PVs.')
    sub = ap.add_subparsers(dest='cmd')
    for name, cmd in COMMANDS.items():
        p = sub.add_parser(name, help=cmd.help)
        for arg, options in cmd.args:
            p.add_argument(arg, **options)
        p.set_defaults(command=cmd)
    return ap


def main(argv):
    import argparse
    ap = _parser()
    args = ap.parse_args(argv)
    if args.cmd is None:
        ap.print_help()
        print()
        demo = COMMANDS['list']._replace(fmt=ROW, header='Demo, Order 5:')
        _run(argparse.Namespace(o=5, n=count(5), tsv=False), demo)
    else:
        _run(args, args.command)


if __name__ == '__main__':
    import sys
    main(sys.argv[1:])
