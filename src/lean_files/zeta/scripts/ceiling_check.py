# B128: the ceiling x*(wall) = R(n)/(2^L - 3^n) < t_n, t_n the least integer x >= 1 with (3x+1)^n < 2^L x^n,
# exact (R < t_n (2^L - 3^n)), for Orders 1..N. Usage: ceiling_check.py N
import sys
p2 = lambda m: (3**m).bit_length()
bad = []
for n in range(1, int(sys.argv[1]) + 1):
    L = p2(n); lo, hi = 0, 1
    while (3*hi+1)**n >= 2**L * hi**n: hi *= 2
    while hi - lo > 1:
        m = (lo + hi) // 2
        if (3*m+1)**n < 2**L * m**n: hi = m
        else: lo = m
    R = sum(3**(n-q-1) * 2**(p2(q)-1) for q in range(n))
    if not R < hi * (2**L - 3**n): bad.append(n)
print('x*(wall) < t_n fails at', bad if bad else 'no Order', 'of 1 ..', sys.argv[1])
