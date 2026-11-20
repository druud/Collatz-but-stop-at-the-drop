# The best of the Order

Lean 4 / Mathlib statements of the paper *Collatz, but stop at the drop: the start words
with the highest drop ratio* (`Project_kb/R_collatz_stop_at_the_drop/R_collatz_stop_at_the_drop_best.tex`),
namespace `BestOfOrder`. Exact statements only; the table of bests is script data
(`scripts/`, `data/`). All results are proved without `sorry`.

The words, the map T and the constants come from the library `AcceleratedCollatz`
(`../accelerated_collatz`), through one bridge file, `BestOfOrder/Bridge.lean`.

| File | Paper | Declarations |
|---|---|---|
| `Bridge.lean` | Lemma 2.2, Theorem 3.2 | `affine`, `mem_class_iff`, `rho_append`, `rho_le_wall`, `rho_eq_wall_iff`, `wall_eq_sum`, `admissible_iff_pow` |
| `CyclePoint.lean` | Theorem A (4.2), Lemma 2.5, Propositions 4.4 and 4.6, Lemma 4.5 | `one_sub_ratio`, `ratio_lt_ratio_iff`, `drops_iff`, `ratio_lt_of_lt`, `cyclePoint_lt_cyclePt`, `cyclePt_length`, `iterate_eq_split`, `prefix_cyclePoint_neg` |
| `StartParts.lean` | Lemma 3.4 | `isKey_of_prefix`, `exists_of_key`, `persistent_append_true` |
| `Dinkelbach.lean` | Lemma 5.1 | `F_strictAnti`, `F_lamStar`, `eq_lamStar_of_F_eq_zero`, `F_ratio_nonneg`, `step_lt` |
| `MeetingSplit.lean` | Theorem C (5.3) | `rho_split`, `split_identity`, `mem_split_iff`, `meet_of_mem`, `mem_of_meet`, `exists_start_iff` |
| `Window.lean` | Theorem B (6.1), the bound by R(n); Remark 2.10 (ties: equal ratios give rho c* = rho* c, so c is a multiple of c*/gcd(c*, rho*)) | `window`, `tie_rho`, `tie_dvd` |
| `Walk.lean` | Lemma 2.4, Lemma 5.3 (the walk), Corollary 3.3, Theorem 6.1 below a prefix | `congruence`, `rho_eq_sum`, `walk`, `tail_bound`, `window_prefix` |

## Build

The Lake packages directory is shared with `accelerated_collatz`
(`packagesDir` in `lakefile.lean`), so its Mathlib and its build are reused:

```sh
cd ../accelerated_collatz && lake exe cache get && lake build   # once
cd ../best_of_order && lake build
```

## Scripts and data

Copies of the scripts the paper cites (originals in the local `_keep/tree_01/`), exact integers throughout:

| File | Paper |
|---|---|
| `scripts/boo.py` | best-first search seeded with the smallest start (Orders 1..124) |
| `scripts/boo_scan.cpp` | the scan over all starts below the window (6 threads, wheel mod 2^28) |
| `scripts/boo_tie_mult.py` | ties of the best (Remark 2.10) by divisibility: the multiples of c*/gcd(c*, rho*) below the window; `boo_tie_mult.py data/best_cert_347.txt` |
| `scripts/boo_ties.cpp` | ties of the best by the tree (Remark 2.10, Orders to 229), and the recheck of one Order: `boo_ties n n` |
| `scripts/boo_obs.py` | checks each best and writes the certificate file; the smallest-start observation |
| `scripts/boo_hubs.py` | the odd parts of the drop values (merging trajectories) |
| `scripts/boo_count.py` | the number of words of each Order (A100982), the words of one Order with $\rho$, $c$, $d$, and Dinkelbach's steps over them (Remarks Order 6, The number of words, The steps) |
| `scripts/ceiling_check.py` | the ceiling x*(wall) < t_n for n <= 2000 |
| `scripts/dinkel_suffix.py` | the backward ranking k0 (Orders 2..21) |
| `scripts/inv_grow.py`, `scripts/inv_hub.py`, `scripts/mitm.py`, `scripts/mitm4.py` | Appendix A (ways that did not work) |
| `data/b402443_347.txt` | the bests, n = 0..347 (OEIS A402443 b-file; a(0) = 2) |
| `data/best_cert_347.txt` | per Order n: c, d = T^L(c), the window W of Theorem B (6.1) |
