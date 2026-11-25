#!/usr/bin/env python3
# Writes AcceleratedCollatz/Zeta/Best/CertData.lean from data/best_cert_378.txt: the rows (n, c, d, W) as a Lean list.
# Run from Lean/accelerated_collatz/zeta:  python3 scripts/cert_lean.py
rows = [l.split() for l in open('data/best_cert_378.txt') if l.strip() and not l.startswith('#')]
with open('../AcceleratedCollatz/Zeta/Best/CertData.lean', 'w') as f:
    f.write('-- SPDX-License-Identifier: MIT\n')
    f.write('import Mathlib.Data.Nat.Notation\n\n')
    f.write('/-!\n  The certificate rows (n, c, d, W) of `data/best_cert_378.txt`, Orders 1..%s; written by\n'
            '  `scripts/cert_lean.py`, not by hand. Checked in `AcceleratedCollatz.Zeta.Best.Certificates`.\n-/\n\n' % rows[-1][0])
    f.write('namespace AcceleratedCollatz.Best\n\n')
    f.write('/-- The rows (n, c, d, W): c the best of Order n as found by the search, d its drop value,\n'
            '    W the window bound. -/\n')
    f.write('def certRows : List (ℕ × ℕ × ℕ × ℕ) := [\n')
    f.write(',\n'.join('  (%s, %s, %s, %s)' % tuple(r) for r in rows))
    f.write(']\n\nend AcceleratedCollatz.Best\n')
print(len(rows), 'rows')
