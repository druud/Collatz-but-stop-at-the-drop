# The best of the Order

Lean 4 / Mathlib statements of the paper *Collatz, but stop at the drop: the start words
with the highest drop ratio* (`Project_kb/R_collatz_stop_at_the_drop/R_collatz_stop_at_the_drop_best.tex`),
namespace `BestOfOrder`. Exact statements only; the table of bests is script data
(`scripts/`, `data/`). All results are proved without `sorry`.

The words, the map T and the constants come from the library `AcceleratedCollatz`
(`../accelerated_collatz`), through one bridge file, `BestOfOrder/Bridge.lean`.

| File | Paper | Declarations |
|---|---|---|
| `Bridge.lean` | Lemma 2.2, Theorem 3.2, Proposition 3.4 | `affine`, `mem_class_iff`, `rho_append`, `rho_le_wall`, `rho_eq_wall_iff`, `wall_eq_sum`, `rho_eq_lower_iff`, `rhoMax_le_mul`, `admissible_iff_pow` |
| `CyclePoint.lean` | Theorem A (4.2), Lemma 2.5, Propositions 4.4, 4.6 and 4.7 (the ceiling), Lemma 4.5 | `one_sub_ratio`, `ratio_lt_ratio_iff`, `drops_iff`, `ratio_lt_of_lt`, `cyclePoint_lt_cyclePt`, `cyclePt_length`, `iterate_eq_split`, `prefix_cyclePoint_neg`, `cyclePt_le_pow`, `cyclePoint_lt_ceiling` |
| `StartParts.lean` | Lemma 3.5 | `isKey_of_prefix`, `exists_of_key`, `persistent_append_true` |
| `Dinkelbach.lean` | Lemma 5.1 | `F_strictAnti`, `F_lamStar`, `eq_lamStar_of_F_eq_zero`, `F_ratio_nonneg`, `step_lt` |
| `MeetingSplit.lean` | Theorem C (5.3) | `rho_split`, `split_identity`, `mem_split_iff`, `meet_of_mem`, `mem_of_meet`, `exists_start_iff`, `admissible_split_iff`, `prefix_pow_of_admissible` |
| `Window.lean` | Theorem B (6.1), the bound by R(n); Corollary 6.2 (where the best lies); Remark 2.10 (ties: equal ratios give rho c* = rho* c, so c is a multiple of c*/gcd(c*, rho*)) | `window`, `window_seed`, `window_seed_half`, `share_ratio_ge`, `tie_rho`, `tie_dvd` |
| `Certificates.lean`, `CertData.lean` | Remark 6.7 (the certificates): each of the 378 rows of `data/best_cert_378.txt` is a word of Order n with that drop value, c the smallest member that drops, and every member of a class of Order n with a higher ratio is below W. Checked by the kernel (`decide +kernel`), no `native_decide`; `CertData.lean` is written by `scripts/cert_lean.py` | `cert_rows`, `cert_of_rowOk`, `scan_spec`, `wallC_eq` |
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
| `scripts/boo_scan.cpp` | the scan over all starts below the window (6 threads, wheel mod 2^28); it counts the prefixes with 3^j < 2^l at which the start has not dropped: with a count of 0 the run does not rest on the width identity |
| `scripts/paper_numbers.py` | recomputes the numbers of the paper and compares each with the text (OK / DIFF / SKIP); the smallest starts from `data/b122442.txt` (`--seeds=FILE` for another copy); `--appendix` reruns the scripts of Appendix A (about 3 minutes), `--beam` also `boo_beam.py 3 8` (long) |
| `scripts/paper_numbers_slow.cpp` | its two slow checks in C++ (GMP), about 2 minutes, 2.4 GB: Table 1 to Order 21, and the node counts of the best-first search for Orders 1..124 (`_tmp/paper_numbers_slow`, the smallest starts from `data/b122442.txt`); `--k0=N` gives k0 for Orders 22..N instead (N <= 32; checked against Table 1 up to 25, about 5 minutes; about 3 times longer per Order) |
| `scripts/cert_lean.py` | writes `BestOfOrder/CertData.lean` from `data/best_cert_378.txt` |
| `scripts/boo_tie_mult.py` | ties of the best (Remark 2.10) by divisibility: the multiples of c*/gcd(c*, rho*) below the window; `boo_tie_mult.py data/best_cert_378.txt` |
| `scripts/boo_ties.cpp` | ties of the best by the tree (Remark 2.10, Orders to 229), and the recheck of one Order: `boo_ties n n` |
| `scripts/boo_obs.py` | checks each best and writes the certificate file; the smallest-start observation |
| `scripts/boo_hubs.py` | the odd parts of the drop values (merging trajectories) |
| `scripts/boo_count.py` | the number of words of each Order (A100982), the words of one Order with $\rho$, $c$, $d$, and Dinkelbach's steps over them (Remarks Order 6, The number of words, The steps) |
| `scripts/ceiling_check.py` | the ceiling x*(wall) < t_n for n <= 2000 (a check; Proposition 4.7 proves it for every n) |
| `scripts/dinkel_suffix.py` | the backward ranking k0 (Orders 2..21; 22..25 by `paper_numbers_slow --k0=25`) |
| `scripts/inv_grow.py`, `scripts/inv_hub.py`, `scripts/mitm.py`, `scripts/mitm4.py` | Appendix A (ways that did not work) |
| `scripts/aim_cross.py`, `scripts/aim_area.py`, `scripts/ideal_lines.py`, `scripts/mitm_search.py`, `scripts/boo_beam.py`, `scripts/boo_cand.py` | Appendix A: crossings of and area against the scaled wall word, ideal lines, the backward search, candidates from earlier Orders (`data/boo_beam_3_8.out`: the output of `boo_beam.py 3 8`) |
| `data/b122442.txt` | the smallest start of each Order: a(n+1) of OEIS A122442, n = 1..400 (the copy the searches used; the OEIS b-file is https://oeis.org/A122442/b122442.txt) |
| `data/b402443_378.txt` | the bests, n = 0..378 (from the scan, `boo_scan`, stopped at Order 378; a(0) = 2) |
| `data/best_cert_378.txt` | per Order n: c, d = T^L(c), the window W of Theorem B (6.1) |
