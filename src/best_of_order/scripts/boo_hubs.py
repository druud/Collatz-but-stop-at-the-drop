# B122: the odd parts of the drop values d = T^L(best) of the bests (b-file of A402443), how many Orders share
# each, and which lie on the trajectory of 27. Usage: boo_hubs.py bfile N
import sys
from collections import defaultdict
p2 = lambda m: (3**m).bit_length()
T = lambda x: (3*x+1)//2 if x & 1 else x//2
odd = lambda x: x >> ((x & -x).bit_length() - 1)
B = {int(a): int(b) for a, b in (l.split() for l in open(sys.argv[1]) if l.strip() and not l.startswith("#"))}; N = int(sys.argv[2])
G = defaultdict(list)
for n in range(1, N + 1):
    d = B[n]
    for _ in range(p2(n)): d = T(d)
    G[odd(d)].append(n)
print(len(G), 'odd parts for', N, 'Orders')
for o, ns in sorted(G.items(), key=lambda t: -len(t[1])):
    if len(ns) >= 3: print(o, len(ns), ns)
print('2 Orders:', sum(len(v) == 2 for v in G.values()), ' 1 Order:', sum(len(v) == 1 for v in G.values()))
t = [27]; x = 27
while x != 1: x = T(x); t.append(x)
on = sorted((o for o in G if o in set(t)), key=t.index)
print('on the trajectory of 27:', on, 'for', sum(len(G[o]) for o in on), 'Orders')
