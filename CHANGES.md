# Changes

The changes to this repository since its first public release, newest
first. Version names (R_65a, R_66, ...) are the authors' own labels.

## After R_104 (24 November 2026)

- The drop zeta draft, Draft (12), 44 pages: Theorem M (Theorem 14.16), the 2-adic starts with
  no drop word as a prefix form a closed null set of Hausdorff and box dimension log_3(3 kappa),
  the entropy of a letter that is a one with chance 1/log2 3; Covering asks that it hold no integer
  x >= 0. Lean: `TNoDropCount` (`noDropCount_mul_le`), the count of the words that never drop.
- The drop zeta draft, Draft (11): Proposition 14.13, the masses are exactly the
  first-drop chances of the letters with chance 1/log2 3, weighed again with chance 1/2
  per letter; the staircase is now Corollary 14.15, read on the floors.
- The drop zeta draft, Draft (10), 41 pages, with index: the best of the Order and the floors
  merged into it; the floors bound the drop ratios from below, the best from above, and both
  now come before the zeta function. The separate best and floors drafts are withdrawn. In Lean,
  the best of the Order moved into `AcceleratedCollatz/Zeta/Best/` (the floors into
  `Zeta/Floor/`), its scripts and data into `zeta/`; `best_of_order/` is gone.
- The drop zeta draft, Draft (9): Proposition 7.5, the primes: the floors are the powers of F = 3/4.
- The drop zeta draft, Draft (8): Section 7, "Compared with zeta".
  Theorem 7.1 (main Theorem F), the explicit formula: the integrated
  renewal count U_1 of the drop map is (u^2/2 + c_1 u + c_2)/mu plus
  one harmonic e^((s_k - 1)u)/(-P'(s_k)(s_k - 1)^2) per pole,
  checked against exact chain counts (Computation 7.2). Theorem 7.3:
  P has no zeros with Re s <= 1 (the prime zeta function has its
  zeros on the other side); Observation 7.4 on the zeros to the
  right; a table of zeta beside Z (18 pages).
- Lean: `TCycleZeroQ`, the zeros for odd q >= 3: with L = p2Q q n,
  L N_q(n) = binom(L, n), that is every word of length L with n ones
  is a rotation of a drop word, iff n is an upper record Order
  (`p2Q_mul_card_eq_choose_iff`); every Order has a drop word, and
  m < n is a split Order iff its floor lies below that of n (never
  equal, q odd).
- The drop zeta draft, Draft (7): Corollary 5.12, the mass of Order n,
  m_n = G(e_n) (alpha/(2(alpha - 1)))^(e_n) kappa^n/(sqrt(2 pi alpha
  (alpha - 1)) n^(3/2)) (1 + O(n^-1/2)), from Theorems 5.9 and 5.10: in
  a log2 plot the masses follow n log2 kappa - (3/2) log2 n, shifted by
  a function of e_n with a total height of 1.
- The floors draft, Draft (9), now public (`R_collatz_stop_at_the_drop_floors.pdf`,
  its source in `src/`): the floors 3^n/2^L of the Orders; the three
  gaps (the intervals of Pythagorean tuning), the counts of OEIS A400061
  by the floors, and the staircase with M. Winkler's rate; in Lean
  `TFloorGaps` and `TRowLength`. Each numbered section and the
  References start on a new page (12 pages).
- Lean: `TMassShareQ`, the shares behind the rate of zeta Theorem 5.10
  (M. Winkler), for odd q >= 3 and any p in a field: with
  P_n(m) = N(m) binom(L - p2(m), n - m)/binom(L, n),
  w(m) = N(m) p^m (1 - p)^(p2(m) - m) and
  Q(j) = binom(p2(j), j) p^j (1 - p)^(p2(j) - j):
  1 - L N(n)/binom(L, n) is the sum of P_n(m) over the split Orders
  (`one_sub_mass_eq_sum_shareQ`); P_n(m) = w(m) Q(n - m)/Q(n) for every
  split Order m and p != 0, 1 (`shareQ_eq`); p2(m) w(m) <= Q(m) for
  0 <= p <= 1 (`p2Q_mul_wQ_le`).
- Lean: `TCycleCountQ`, the identity of `TCycleCount` for every odd
  q >= 3 (M. Winkler's question): with L = p2Q q n the least L with
  q^n < 2^L and N_q(n) the drop words of Order n,
  binom(L, n) = L N_q(n) + sum over 1 <= m < n with
  p2Q q m + p2Q q (n - m) = p2Q q n of N_q(m) binom(p2Q q (n - m), n - m)
  (`choose_p2Q_eq_split`); the condition iff
  2^p2Q q m q^n < 2^p2Q q n q^m (`mem_splitOrdersQ_iff`). The proof
  for q = 3 uses only that 3 is odd: distinct prefixes have distinct
  levels (`lvQ_inj`, from q^a 2^x != q^b 2^y for a < b).
- The drop zeta draft: a new page for Main results, each section and
  the References (16 pages); Figure 1 in Section 5, the mass per Order
  L N(n)/binom(L, n) against e_n for the Orders 1 to 399 with the
  staircase G (its jumps to Order 5000) and the upper record Orders
  (`media/mass_tikz.py`).

## R_104 (24 November 2026)

- Lean: `TRowLength`, the row lengths of the triangle by records (draft
  A900014): the largest number of parts m_1 + ... + m_k = n with
  p2(m_1) + ... + p2(m_k) = p2(n) is min over d >= 1 of
  d p2(n) - n (p2(d) - 1) (`rowLength_eq_min`); the bound by
  2^(d p2(m)) > 3^(dm) >= 2^(m (p2(d) - 1)), the split that reaches it
  along the record walk of `TFloorGaps`.
- Lean: `TFloorGaps`, the three gaps of the floors 3^n/2^p2(n) in
  exact rationals: with the lowest and highest floor of Orders 1 to N
  at a and b, the next floor above that of Order m is that of m + a,
  m - b or m + a - b, at the end ratios 2 theta_a, 1/theta_b and their
  product (`gap_up`, `gap_down`, `gap_mid`), and a + b >= N + 1; each
  case from the product rule theta_(x+y) in {theta_x theta_y,
  2 theta_x theta_y} (`blockFactor_add`) and the two extremes. Also
  a + b is the next record Order (`next_record`, `extremes_until`).
- The drop zeta draft, Draft (4): Theorem 5.9, the limit L N(n)/binom(L, n) - G(e_n) -> 0
  (the share of the words with no drop rotation, OEIS A400061, tends to
  the staircase) and with it the kappa law for N(n)/3^n; only the 1/70
  for the Orders 100 to 399 stays an observation. Draft (5): Figure 2,
  the floors 3^n/2^p2(n) of Orders 0 to 40 with the upper and lower
  record Orders (`media/floors_tikz.py`); the figures stay in their
  section (placeins), 12 pages. Draft (6): Theorem 5.10 (M. Winkler,
  private communication), the rate O(n^-1/2) of Theorem 5.9, with
  liminf 0 and limsup p of the share; the line "No rate of convergence
  is proved" gone.
- `media/`: the pictures `drop_tree.svg` (the drop tree of Orders 1 to
  6), `a400061_floors.svg` and `a400061_staircase.svg` (the Floors and
  Staircase pictures of OEIS A400061, with their scripts).

## R_103 (24 November 2026)

- The drop zeta draft, Draft (2): the count of the words with no
  drop rotation, binomial(p2(n), n) - p2(n) A100982(n), is OEIS
  A400061. Draft (3): Observation 5.9 within 1/70 of the staircase
  (was 1/40, measured against the staircase cut at Order 399).

## R_102 (24 November 2026)

- New draft beside the series, *The drop zeta function* (Draft (1),
  10 pages; `R_collatz_stop_at_the_drop_zeta.pdf`, source in `src/`):
  Z = 1/(1 - P), P the sum over the drop words; P is entire and Z
  meromorphic without zeros, with its pole at s = 1 (Terras); one
  pole per horizontal band, none with Re s >= 1 but s = 1, all on one
  curve sampled by the rotation by log2 3; the identity
  C(p2(n), n) = p2(n) a(n) + sum of a(m) C(p2(n - m), n - m) of the
  Lean module `TCycleCount`; the jumps sum p = 1/log2 3; the octave
  clock (figure).

- Lean, new module `TCycleCount`: C(p2(n), n) = p2(n) a(n) + the sum
  of a(m) C(p2(n - m), n - m) over the m with 1 <= m < n and
  p2(m) + p2(n - m) = p2(n), a = A100982 (`choose_p2_eq_split`);
  that condition is 2^p2(m) 3^n < 2^p2(n) 3^m (`mem_splitOrders_iff`).

- The pages `building.html`, `drop_tree.html` and `drop_turn.html`
  moved into the folder `media/`; `building.html` now opens at
  druud.github.io/Collatz-but-stop-at-the-drop/media/building.html.

- The best paper, Draft (46): the search to Order 378 was rerun with
  the width-identity count (46 hours on 6 threads): the count is 0,
  with the same best, drop value and window for every Order, so the
  bests no longer rest on the width identity (Chapter 6 and the
  section The Lean formalization). Its output is
  `data/boo_scan_378.out` of the Lean package best_of_order.

- Paper 2 and the best paper, Draft (45): cite Terras 1976,
  Proposition 1.7, for the drop criterion (a member drops at the end
  of its word if and only if it is larger than the cycle point).

- Paper 3 (draft), Chapter 2: cites Erdős and Lewin 1996 (d-complete
  sequences; only {2, 3}) and Erdős Problem 1110 (van Doorn: Theorem 2
  of Blecksmith, McCallum and Selfridge answers it).
  Also Crandall 1978 (Math. Comp. 32), Theorem 7.1: the same staircase
  sum and, read to 1, the link with 3x + 1 (29 pages). Older still:
  Terras 1976, Theorem 1.1, has the sum term by term; named first.

- The best paper, Draft (44): Table 1 extended to Order 28
  (`scripts/paper_numbers_slow --k0=28`), with L/2 < k0 < 4L/5 for
  Orders 15 to 28; the remark "Both sides in turns" measured over
  all words to Order 26 (`scripts/both_sides.cpp`): 1 or 2 words
  pass both tests at each cut from Order 14 on.

- The best paper, Draft (43): the bests of Orders 1 to 378, each
  with a certificate proved in Lean (`src/best_of_order/data/
  best_cert_378.txt`); the smallest start is the best for 307 of
  them, none has a tie.

- The best paper, Draft (42): theta(s_0) >= 2 theta(c*)/n for
  n >= 3 (Corollary 6.2; Lean `share_ratio_ge`); Table 1 extended to
  Order 25 (`scripts/paper_numbers_slow --k0=25`), with
  L/2 < k0 < 4L/5 for Orders 15 to 25; the OEIS A-numbers in the
  index link to the References.

- The best paper, Draft (41): the ceiling x* < t_n is proved for
  every Order and every word (Proposition 4.7; Lean
  `cyclePoint_lt_ceiling`), so one open question is closed; the index
  keeps an item with its subitems in one column.

- The best paper, Draft (40): Corollary 6.2 in the abstract and in
  Theorem B (c* < n s_0/2 for n >= 3), and both of its bounds in Lean
  (`rhoMax_le_mul`, `window_seed_half`). `src/best_of_order/data/`
  holds the b-file of A122442 (n = 1..400) that the searches used;
  the scripts read it from there. `scripts/paper_numbers.py
  --appendix` reruns the scripts of Appendix A against the text,
  `--beam` also `boo_beam.py 3 8`.

## R_101 (20 November 2026)

- Paper 3, draft: "Draft: R_101" (28 pages).

- A new paper beside the series, a draft: *Collatz, but stop at the
  drop: the start words with the highest drop ratio*. The best of the
  Order (the class id c > 1 with the highest T^L(c)/c, OEIS A402443)
  is the word whose cycle point lies closest to c; a window outside
  which no start can win; the meeting split of the search; the bests
  of Orders 1 to 347, each with a certificate. Lean package
  `src/best_of_order/` (on top of `lean_files/`), with its scripts
  and data; `src/best_of_order.zip`.
  Draft (38): Lean checks all 347 certificate lines by the kernel
  (`cert_rows`); `scripts/paper_numbers.py` recomputes the numbers of
  the paper against its text, and Appendix A's inverse-tree line is
  corrected by it (21 of the 106 bests, 20% against 28%: no excess).
  Draft (39): the lower wall (Proposition 3.4) and where the best
  lies (Corollary 6.2: s_0 <= c* <= s_0 R(n)/(3^n - 2^n), and
  c* < n s_0/2 for n >= 3; Lean `window_seed`); Appendix A's numbers
  rerun, two reworded, their scripts added;
  `scripts/paper_numbers_slow.cpp` for the two slow checks.

- Paper 3, a new Chapter 3, "The words as one tree": the admissible
  words of all Orders as the leaves of one binary tree (figure for
  Orders 1 to 6, from tree_tikz.py); proved on paper: the subtree
  below a prefix depends only on its counts; the words up to Order N
  with the alive prefixes at N + 1 odd steps form a complete code
  (weights 2^(1 - l) add up to 1, Terras's density theorem in the
  limit); those prefixes number a(N + 1). The best of each Order
  (largest T^L(c)/c, the smallest relative margin in the width
  identity): 5, 3, 11, 7, 39, 347, ... (measured). Later chapters
  are renumbered.

- drop_tree.html: the same tree as a page, with options.
- drop_turn.html: the words of one Order as turns around the unit circle; its Order 6 view is the picture on the title page of the paper beside the series.

- Paper 3, "The odd part at the drop": the Lean names of TOddPartDrop;
  S and E bounded in rationals by the survivors' share, 82 and 87
  certified partial quotients (Order 3000).

- Lean: TOddPartDrop (`orderOf_two_zmod_three_pow`: 2 has order
  2 3^n mod 3^(n+1); `exists_odd_part_at_drop`: every odd part coprime
  to 6 in every drop class; `exists_trailing_class`).

- Paper 3, Ch. 4: a new subsection "The odd part at the drop": the
  split of a class by the trailing zeros of the drop value; every class
  reaches every odd number coprime to 6 (2 a primitive root mod 3^n);
  the count per odd part grows by S = (3/4) E per binary digit, E the
  average of 2^L/3^n, as continued fractions (not (3/2) log 2); z and 2z + 1 with the same
  odd part at the drop (TPairLink); three OEIS references (A007310,
  A067745, A122790).

- Lean: TPairLink (`pair_link`, `pair_link_behind`, `pair_link_double`:
  the direct route of z and 2z + 1, word 1^a 0 1 ...).

- Paper 3, Ch. 4, merging paths: the gap of at least 3 steps between
  the drop of x and the meeting of x, x + 1 does not go on beyond 2^21:
  x = 2244603 meets x + 1 at step 55, 2 steps after its drop, and
  x = 100335611 at step 39, before it drops (164 such odd x below 2^31).
- Lean: TRunCoord (`odd_run_end_shift`, `one_in_front`,
  `run_coord_step`, `run_coord_iterate`: a run in one step, the run
  coordinate) and TFlip (`point_of_reach_one`, `flip_digit`: the flip of
  one parity digit, in the integers).

- Paper 3, Ch. 4: a new subsection "Periodic stretches and merging
  paths": parity bits as 2-adic digits, the cycle point of a repeated
  word, the shift identity after a periodic stretch; the stretches in
  the record climbs come with the density of odd steps; two paths merge
  in a pair o, 3o + 1, and x, x + 1 meet at least 3 steps after the drop
  of x (measured below 2^21; exactly 3 for x = 5 mod 32, in Lean).
- Lean: TMerge (`tStep_eq_tStep_iff`, `merge_thirtytwo_add_five`).

- Paper 3, references: the three-gap theorem now cites Sós (1958) and
  Świerczkowski (1958); Levi ben Gershon's result on 2^a 3^b differing
  by 1 also cites Simonson (2000, p. 245) for the statement and
  Carlebach (1910) for the Latin text.

## R_100 (13 November 2026)

- Paper 3, draft: "Draft: R_100".

- Paper 3, draft (23 pages): an abstract, "Main results" (Theorems A
  to D: the largest rho, powers of 2 and 3, the n-th 3-smooth number,
  three letters) and "What was known", as in paper 2.
- Paper 3, Ch. 4: the gap-ratio records over x >= 2 (13 starts below
  2^46; x = 1 left out, as drop(1) = 1 gives 0), as in OEIS A398772.
- Paper 3, a cold read and a claim audit: the slack is half the sum
  of the lower deficits; M counts the letters up to the stop, the last
  included; the count 2 A100982(m) is of the letter words of the
  product rule; the range check is a hypothesis, not a named one, and
  Table A says so; "measured" added where a claim was computed only;
  smaller fixes of wording and references. The early stop of Ch. 7 is
  named: equivalent to the Collatz conjecture, at a merge before the
  drop.
- Paper 3, Ch. 4, "With the zeros kept": the odd step as
  Z -> 3Z + 2^nu(Z), the trailing 0-bits kept; Z_n = 3^n c + rho, and
  c drops when the odd part of Z_n is below c. Measured below 2^20:
  half the class ids have an even drop value and much more slack (47
  from below 2 to above 20); the tight ones left have an odd drop value.
  Halving keeps the numbers small and hides this race.
- Lean, TEvenDrop (in the root): for x with an admissible word of
  Order n >= 2 and length L, n <= 3x: T^L(x) < 2x, and if T^L(x) is
  even, T^(L+1)(x) < x (drop_succ_of_even). Paper 3, Ch. 4 cites it:
  one extra zero is always enough; the hard case is an odd value at
  the end of the word. Table A, row 4.
- Paper 3: Terras (1976) and Garner (1981) read. The largest rho, its
  unique word and the bound W(n) of Theorem A are Terras's (Mini-Max
  theorem 2.6, Thm. 2.10; his omega/(2 - mu) equals rho_max/d_23 at
  every upper record Order to 1636, his Table C lists W(n) + 1); new
  are the records proved and the range. T^L(x) < 2x follows from
  Garner's estimate. Abstract, Theorem A, Ch. 3, Ch. 4 and "What was
  known" corrected; Garner added to the references.
- Paper 3, Ch. 2: the staircase as a special 3-smooth representation
  of level n - 1 (Blecksmith, McCallum and Selfridge 1998). B39.
- Paper 3, Ch. 4, "The drop amount over the blocks": with v_i the value
  at the start of block B_i, k(c) = sum (k(c_i) + q_i d_i) - (c+1)/2;
  the tight class ids hand their margins on along the path of 27. By
  induction on the Order this settles every word with sum q_i d_i >=
  (c+1)/2, every word with a block 0 among them (measured: 32698 of the
  56507 class ids below 2*10^6). No fixed depth settles all: for the
  words 1 B with B the whole word of T(c), the hypothesis needed is the
  width identity of c itself. The d = 1 blocks 0 and 10 are the only
  ones (Levi ben Gershon). B43, B45, B46.
- Lean, TRhinSplit (in the root): 3 widthBound(n) + 1 <= 2^p2(n) at
  every Order up to 10^60, and at every Order under RhinBound 1 14. Paper
  3, Ch. 4, "The bound of a split", cites it (was: computed to Order
  3000). Table A, row 4.
- Lean, TGersonides (in the root): 3^b + 1 = 2^a only for (a, b) =
  (1, 0), (2, 1), and 2^a + 1 = 3^b only for (1, 1), (3, 2) (Levi ben
  Gershon, De numeris harmonicis, 1343). Paper 3, Ch. 4. Table A, row 4.
- Paper 3: 25 pages.
- Paper 3, notation (B53 to B57): i is the exponent of 2 and j that of
  3 everywhere (the grid 2^i 3^j, as in Theorem B and OEIS A014121; also
  in paper 2's Mintz passage); one letter, one meaning per chapter
  (the drop amount delta(c), start values V_i, d_23(B_i), L for p_2(n),
  n_1 + n_2 for a split, y < z for neighbours, and others); undefined
  symbols defined at first use; unused macros removed.

## R_99 (11 November 2026)

- Paper 3, draft: "Draft: R_99".

- Paper 3, draft, Ch. 4: the factored gap ratio (gap_ratio_eq) and the
  sieve of the gap-ratio record search, sound for s <= 16 with no
  hypothesis (sieve_skip, sieve_skip_16; Lean TA398772, OEIS A398772);
  TA398772 in Table A, row 4. At Order > 0 the skipped start has a
  strictly larger gap ratio (sieve_skip_lt, sieve_skip_16_lt); at
  Order 0 (even starts) both are 1/2.
- Lean, TRhoBound: rho < n 3^(n-1) for admissible words of Order
  n >= 2 (rho_lt_of_admissible; Order 1 is the word 10, rho = 1).
- Paper 3, draft, Ch. 2 and 3: the strict forms, rho < n 3^(n-1) from
  Order 2 on, and a later Order with a larger block factor has a
  larger ratio rho_max/d_23 (rmax_lt_of_lt_of_blockFactor_lt).

## R_98 (10 November 2026)

- Range check A20 (5-10 November 2026, 0 fails): every x with
  1 < x <= 294401822513350 drops at its coefficient stopping time; with
  classDropsAt_le_64497106 (TFiniteCheckNext) this gives ClassDrops at
  every Order up to 64497106 (was 10781273).
- Lean, TGapRecord: a gap-ratio record x == 3 (mod 4) is the class id
  of its word up to Order 64497106
  (eq_classId_of_gapRecord_mod4_le_64497106; also
  eq_classId_of_gapRecord_le_64497106 and
  eq_classId_of_gapRecord_mod4_of_classDrops).
- Paper 3, draft: Ch. 3 and Ch. 4 at the new bound 64497106, Table A
  rows 3 and 4; "Draft: R_98".
- Paper 2: the version on Zenodo (R_75) is kept as
  R_collatz_stop_at_the_drop_2_zenodo.pdf, as for paper 1.
- README: the DOIs of the first Zenodo versions beside the concept DOIs.

## R_97 (5 November 2026)

- Paper 3, draft: Ch. 7 cites stops_iff (every odd k >= 3 has a stop
  iff every path reaches 1), stop_of_coeff and density (Terras 1976,
  Everett 1977 in the bibliography); Appendix A lists the extracts
  A349414Run and A349414Count beside TUds. 21 pages (Ch. 7 on two).
- Lean, side result: A349414Pre (self-contained extract, Mathlib and
  the extracts Rule505 and A349414Run only): the entry h 4 1 m =
  (4^(m+1) - 1)/3 of A401763 (1, 5, 21, 85, ...) is the odd T-preimage
  of 2^(2m+1) (tPre_odd_eq, T_h41), A282798(2m+1) + 1
  (axisVal_odd_add_one; A282798(2m+3) = 4 h 4 1 m) and the offset of
  the letter power S^(m+1) (pow_S_tPre); the letter S takes
  h 4 1 (m+1) to h 4 1 m (st_h41), so these preimages form one S-chain
  85 -> 21 -> 5 -> 1 (st_iter_h41); both extracts define the same T
  (T_eq).

## R_96 (5 November 2026)

- Lean: TFiniteCheckNext: five more steps of the Stern-Brocot walk
  (sbWalk_107): 10781274 is an upper record Order, p2(10781274) =
  17087915, none lies in (10781274, 64497107), widthBound 10781274 =
  294401822513350; so a range check up to 294401822513350 gives
  ClassDrops at every Order up to 64497106 (classDropsAt_le_64497106).
- Lean, side result: A349414Count (self-contained extract, Mathlib
  and ChainDecomposition only): the stop words of the A349414 run
  with a >= 1 letters U or D number 2 A100982(a) (stop_count), S the
  only one with none (stop_count_zero); with U -> 1, D -> 10, S -> 00
  a stop word is an admissible PV v or v0, and each v gives both.

## R_95 (5 November 2026)

- Lean, side result: A349414Run: the run stops for every odd k >= 3
  iff every T-path reaches 1 (stops_iff); the letter powers U^n, D^n,
  S^n in closed form with h r s n of A401763 (run_U, run_D, run_S,
  h_mul); the starts of a word form one class (run_class); the run
  reads the parities of T k, T^2 k, .. (path), binomially spread
  (oc_eq); a Terras-type density: the share of odd k (mod 2^(E+1))
  with no word of e <= E below product 1 goes to 0 (density), and
  such a word stops every k > 2^e 3^m in its class (stop_of_coeff).

## R_94 (5 November 2026)

- Lean, side result: TGapRecord: a gap-ratio record whose word has
  Order > 0 and class id > 1 is that class id, where ClassDrops holds
  at its Order (eq_classId_of_gapRecord); so up to Order 10781273
  from the range check alone (eq_classId_of_gapRecord_le_10781273);
  for a record x == 3 (mod 4) both conditions hold
  (eq_classId_of_gapRecord_mod4).
- Lean, side result: Rule505 (self-contained extract, Mathlib only):
  Barker's two conjectured closed forms of A282798 (Rule 505, the
  x-axis) proved, a(n) = 2^(n+1) - 1 for n even, 2 (2^n - 2)/3 for n
  odd (axisVal_eq), and his recurrence (axisVal_rec); a(n) + 1 is the
  T-preimage of 2^n of the reverse steps (axisVal_add_one).
- Lean, side result: A349414Run (self-contained extract, Mathlib
  only): the A349414 map on odd k run to the first value below k
  stops when k drops (stops_of_drops); a stop by D is the drop
  (stop_D), a stop by S a merge before it (stop_S); the stop has
  3^m < 2^e (pow_lt_of_stop).
- Paper 3, draft: an even x drops at once, x = 4i + 1 to 3i + 1; each
  record x == 3 (mod 4) is the class id of its word up to Order
  10781273 (eq_classId_of_gapRecord_mod4); 14 record starts of the
  gap ratio below 2^46.

## R_92 (4 November 2026)

- Lean, side result: TUpperRecord: up to Order 971 the new lows of
  (2^L - 3^n)/2^L are at 1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306,
  971 (upperRecord_iff); p2(n + 53) = p2(n) + 84 for n < 306, and
  p2(359) = p2(306) + 85 (pT_add_53, pT_359).
- Paper 3, draft: cites TGapRatio and TUpperRecord; 14 record starts
  of the gap ratio below 2^43.

## R_91 (3 November 2026)

- Lean, side result: TGapRatio: at the drop, 2^L (x - y) + rho = d x
  (gap_identity); of two starts with the same parity word, the
  smaller has the smaller gap ratio (gap_mul_lt_of_lt), so each
  record of A398772 is the least start of its word.
- Paper 3, draft: the ratios on E are given as fractions only.
- Paper 3, draft: no record low of the gap ratio between 10^11 and
  10^12; the rows of A398772 are complete below 10^12.

## R_90 (3 November 2026)

- Paper 3, draft: on E, the scan below 10^11 finds no other failure;
  its minima at blocks 2 and 3 fall further out; c/p < 3/2 at the
  word of 47. Belaga's bound in rationals: 2^l <= (3 + d/m)^k.
- Paper 3, draft: the failure of E at i = 1 as a test on a start and its
  drop, 3*2^L*(x - y) < d*(x + 1); the record lows of the gap-ratio
  (x - y)/x are OEIS A398772, their Orders the upper record Orders.

## R_89 (2 November 2026)

- Paper 2, next version: the lower bound on a(n) also follows from
  Nakamigawa and Tokushige 2012, as Winkler's paper notes.
- Lean, side result: TPrefixBlockFail: backlog item E is false. The
  word of 31 is 1 B 0, of Order 35, with B the word of 47, its first
  block; 31 d(B) < rho(B) (not_prefixBlockBound_47,
  not_lt_classId_31). The width identity is not touched. Also
  n <= 2 d(n) for the Orders below 2^10 (order_le_two_mul_d_23).
- Paper 3, draft: the chapter on the cycle points of the blocks says
  that this statement fails.
- Lean, side result: TPrefixBlockRun, backlog item E at the first
  block for the words B = 1^n 0^m with 3^n < 2^(n+m): E holds, or
  T(c(1B)) is an integer cycle point with word B
  (prefixBlockBound_oneRun_or). TPrefixBlockMod3: T(c(1B)) is
  the first of c(B), c(B)+2^L, c(B)+2^(L+1) that is 2 (mod 3)
  (tStep_classId_cons_eq); if it is not c(B), E follows from
  n <= 2 d(B) (prefixBlockBound_of_lt_admissible). rho_oneRun_le:
  1^n 0^m has the least rho of its Order.
- Paper 3, draft: Belaga's perigee bound cited beside tau, with
  Kaneda's short proof; tau(k) is at most Belaga's bound at d = 1.
- Paper 1, next version: "How to read this paper" says where the
  script, building.html, the Lean files and the sources are. The
  version on Zenodo is kept as
  R_collatz_stop_at_the_drop_1_zenodo.pdf.

## R_87 (31 October 2026)

- Lean, side results: TA399760, for OEIS A399760 read up to the
  drop: the word of 4n-1 starts with A001511(n)+1 ones and a 0
  (take_tBits_four_mul_sub_one, unconditional); under an
  admissible drop word L = A020914(A000120(a(n)))
  (a399760_length), so a(n) fixes the word; first occurrences iff
  4n-1 < 2^L when the smaller 4m-1 drop at admissible words
  (a399760_first_oddWord_iff). TPrefixBlock: backlog item E at the
  first block, c(1B) d(B) > rho(B), gives the drop of B's class
  when 3c(1B)+1 <= 2^(1+|B|) (classDrop_of_prefixBlockBound); E
  itself stays open.

## R_86 (30 October 2026)

- Lean, side results for the OEIS entries, read up to the drop:
  TSurvivors: the classes mod 2^k not dropped after k steps,
  counted by A076227 (card_survivorSet). TDropPeriod: A399760's
  period 2^(L-2) when 4n-1 drops at L with an admissible word
  (a399760_period). TMonksDrop: a conjugacy to Monks' T_{A,B}
  read up to the drop (monksConj_drop, monksConj_two_mul).
  TMonksXi: Monks' 2-adic reading as a rational, in integers
  and rationals only; A401592's a(2n) = 2 a(n)
  (monksQ_isXi_two_mul) and A401593's denominator dividing
  2^(3*2^c) - 1 once 2^c is at least the odd steps over the drop
  chain (monksQ_isXi, monksQ_isXi_of_dropOdd).

## R_85 (29 October 2026)

- Lean: TChristoffel. At a record Order n with fraction P/n the
  first P letters of the first word are the upper Christoffel
  word of slope n/(P - n) (take_firstWord_recordFrac; all of it
  at an upper record Order, firstWord_upperRecord, all but the
  final halving at a lower one, firstBody_lowerRecord), and n and
  P are coprime (RecordFrac.coprime). Paper 3, Ch. 3 cites it,
  its Appendix A lists it; still 19 pages.

## R_84 (29 October 2026)

- Paper 3 on the site as "Draft: R_84" (29 October 2026; the
  Christoffel remark checked against the book; first as "Draft:
  R_83" the same day).
- Paper 3: subtitle "The game on the grid of 2^j 3^i"; the
  author line is the name only, Claude credited in Ch. 1; the
  ruler gap (now Ch. 8) moved after the three letters (Ch. 7),
  the minimal class ids now Ch. 6; Ch. 5 is "The n-th 3-smooth
  number, without the list", Ch. 7 "Three letters: the stop of
  A324245"; Ch. 9, "Shares and ratios" reworded.
- Paper 3, Ch. 3: at a record Order the first word is a
  Christoffel word (Berstel, Lauve, Reutenauer, Saliola 2008),
  the upper one of slope n/(P - n), checked against the book's
  Definition 1.1.
  Ch. 5: Shanks (1954) and Jackson and Matthews (JIS 5, 02.2.7)
  as the integer-only precedent. 19 pages.

## R_82 (29 October 2026)

- Paper 3 is on the site as a draft, "Draft: R_82" on its front
  page, without a date: `R_collatz_stop_at_the_drop_3.pdf`, its
  source and index in `src/` (first as "Draft: R_81", 28 October
  2026).
- Paper 3, Ch. 2 ("Over the power series in q"): Monks' Table 2,
  with the coefficients as binary digits, is OEIS A389685; cited,
  with an index entry.

## R_81 (28 October 2026)

- Papers 1 and 2: the front page reads "Preprint, October 2026".
- Lean, `TMonksQ`: K. G. Monks' maps T_{A,B} on the power
  series over F_2 (JIS 28, 25.6.8). After L steps,
  q^L T^L(x) = A^n x + B rho_A, with rho_A the staircase sum
  of paper 2 with 2 -> q and 3 -> A (`X_pow_mul_monksT_iterate`);
  for A = 1 the map is the shift conjugated by B,
  T_{1,B}(B y) = B sigma(y) (`monksT_one_mul`).

## R_80 (28 October 2026)

- Lean, `TSubwordJoint`: the admissible words counted by start
  and end together. A start that stays above 1 (every nonempty
  prefix has level > 1) is never cut by a first passage, so the
  suffix identity of `TSubword` keeps its form with the start
  carried along (`joint_first_passage`); it gives the words of
  Order n that start with 1 :: y' and end with x from lower
  Orders (`jointAdm_rec`). These counts are what the subword
  counts of length 4 and 5 across the end of a word need.

## R_79 (28 October 2026)

- Lean, `TSubword`: subwords of the admissible words, counted
  by first passage (after Florez, Junes, Montoya and Ramirez, JIS
  28, 25.1.6, who count subwords of length up to 5 in Dyck paths).
  Cutting the words that start with 1 at their first passage below
  1, as for the count a(n), gives two identities in binomials: one
  for the occurrences of any subword s in the words of Order n
  (`occ_first_passage`), one for the words of Order n that end with
  a given x (`suffix_first_passage`); each gives its Order-n part
  from lower Orders (`occAdm_rec`, `sufAdm_rec`). `TBinomial`
  states the first-passage split as two lemmas
  (`image_firstPassageSplits`, `injOn_firstPassageSplits`).
- Lean, `TSubwordSuffix`: the admissible words of Order n that
  end in 100 number a(n - 1) (`sufAdm_hundred`, n >= 2); those
  that end in 10 number a(n - 1) if p2(n) = p2(n - 1) + 1, else
  none (`sufAdm_ten`). Proof by the last-1 decomposition: a word
  ending in 1 0^j is a persistent word of Order n - 1 completed;
  the longest persistent words are the admissible words without
  their last 0 (`card_persLen_max`), and when p2 steps by 1 the
  next shorter ones are as many (`card_persLen_pred`).
- Lean, `TSubwordCycle`: the cycle lemma at the record Orders. At
  an upper record Order n every word of length p2(n) with n ones
  has exactly one admissible rotation, the one from its last lowest
  point (`exists_admissible_rotate`, `not_admissible_rotate`), so
  p2(n) a(n) = C(p2(n), n) (`p2_mul_card_admSet`: M. Winkler's
  upper bound, attained). At a lower record Order the words of
  length p2(n) - 1 have exactly one persistent rotation each, so
  (p2(n) - 1) a(n) = C(p2(n) - 1, n) (`pred_p2_mul_card_admSet`).
  Counted around the cycle, a subword s occurs
  C(L - |s|, n - order s) times in all these words together
  (`sum_cycOcc_admSet`, `sum_cycOcc_persLen`); the plain count is
  that less the occurrences across the end
  (`occAdm_add_wrap_of_upperRecord`, `occAdm_add_wrap_of_lowerRecord`).
- Lean, `TSubwordShort`: at an upper record Order n >= 2 the
  subwords of length at most 3 explicitly
  (`occAdm_short_of_upperRecord`): every admissible word of Order
  n >= 2 starts with 11 (`prefix_true_true`) and ends in 0, so with
  L = p2(n) the occurrences are C(L - |s|, n - order s) less a(n)
  for 01 and 011, a(n) - E for 001, E for 101 and nothing for the
  others, E being the count of the words ending in 10
  (`sufAdm_ten`).

## R_78 (27 October 2026)

- Lean, the walks of `PowDiffFar` run by the kernel to 10^200:
  each walk in four stretches (`PowDiffFarRhin1` to
  `PowDiffFarRhin4`, `PowDiffFarLow1` to `PowDiffFarLow4`), joined
  in `PowDiffFarCheck`: min(2^i, 3^j) <= p2(j)^2 |2^i - 3^j| for
  1 <= j <= 10^200. Each stretch imports the one before, so
  `lake build` runs them one after the other. The stretches take
  the bracket ends as literals from `PowDiffFarBracket` (14
  kernel-checked chunks of squarings, each from a literal state).

## R_77 (27 October 2026)

- Lean, three new files for every odd multiplier q >= 3 (the
  q-family of paper 2's chain decomposition): `TBracketCountQ`,
  `TChainParseQ`, `TBracketDropQ`; with them every statement of
  paper 2's chapter on the chain decomposition has its form for
  every odd q.
- Lean, `PowDiffFar.lean`: the two walk bounds for any certified
  range (the step towards checks past 10^60).

## R_76 (27 October 2026)

- Lean, three new files outside the papers: `PowDiff.lean` proves
  the numbers |2^i - 3^j| up to the 3000th term of A014121
  (328256967394000206715): A014121 (Kevin Ryde's table of 3000
  terms is right) and A363999 (2891 terms), by a congruence sieve;
  `PowDiffRhin.lean` decides every number under `RhinInt`, an
  integer form of Rhin's bound (no reals);
  `PowDiffWalk.lean` gives the bound min(2^i, 3^j) <= p2(j)^2
  |2^i - 3^j| for j <= 10^60 without it.
- `src/lean_files/.gitignore`: `.lake/`, macOS files and text clippings.

## R_75 (25 October 2026)

- Both papers on Zenodo: paper 1, https://doi.org/10.5281/zenodo.23631044,
  paper 2, https://doi.org/10.5281/zenodo.23631547. Each DOI is on
  its paper's title page and in the other paper's bibliography. The
  README gives the DOIs for all versions.
- Both papers, layout: 10pt type, wider side margins, clearer
  key-term boxes; small fixes to two figures and one sentence.
  Paper 2 now has 33 pages. No change to the mathematics.

## R_74 and R_74a (24 and 25 October 2026)

- Paper 2 will be published on Zenodo instead of arXiv. The
  arXiv-only copy of its source (`src/R_collatz_stop_at_the_drop_2_arXiv.tex`
  and its `.ind`) is removed.
- Paper 2, new front matter, so that what is new is easy to find:
  - an abstract (page 2): what was known, then four numbered new
    results (chains, trees, sweeps, a finite check), then the Lean
    formalization;
  - a page "Main results" with Theorems A to D (chain decomposition,
    bracket trees, sweeps, the finite check of Terras's
    Conjecture 2.9), and "What was known".
- Paper 2, prior work: Terras proved his Conjecture 2.9 for
  coefficient stopping times below 2593, Garner (1981) below
  105,000, that is, for Orders up to 1635 and 66,246. The finite
  check of paper 2 reaches Order 10,781,273, coefficient stopping
  time 17,087,914. Said in the abstract, Theorem D, "What was known"
  and the chapter "What is still open"; the range is new, the method
  is in the spirit of theirs. New references: Boehm and Sontacchi
  (1978), Everett (1977), Garner (1981).
- Paper 2, the abstract's first paragraph (M. Winkler): an
  admissible word gives a residue class whose sufficiently large
  members first fall below their start at the end of the word. The
  earlier wording could be read as saying more, namely the open
  width identity.
- Paper 1: the AI assistance is no longer on the title page; "How
  to read this paper" names it, as before.
- Paper 2: the AI assistance is named under "Contributions" instead
  of on the title page.

## R_73 (22 October 2026)

- Lean: new module TTerras, Terras's theorem: almost every x drops
  under T (`terras_density`: the share of the x < N that never drop
  tends to 0). An elementary count of residues mod 2^m, no
  probability.
- Paper 2, Table 7 (the Lean files): a row for TTerras, and "all
  148" in the caption. Still 33 pages.
- Lean: one module header corrected (TSternBrocotConvQ named two
  theorems that do not exist). No statement or proof changed.

## R_72 (21 October 2026)

- Paper 2: its table of Lean files has a row for TUds, TUdsDrop and
  TUdsCount; "all 147".

## R_71 (21 October 2026)

- Lean, three new modules on the map of OEIS A324245 with its
  letters U, D and S (not cited in the papers):
  - TUds: the value after the letters as 2^b z = 3^M k + c; for all
    large k the stop is at the first prefix with product below 1;
    the odd starts of a letter word are one class modulo 2^(b+1).
  - TUdsDrop: M is at most the Order of the drop, with equality
    exactly for a stop by D; a stop by S is a merge before the
    drop; no stop is by U.
  - TUdsCount: for m >= 1 there are 2 A100982(m) letter words of
    the product rule with M = m, half of them with p2(m) bits.

## R_68a (21 October 2026)

- Lean, one new module, TCongruenceSplit: rho of a concatenation;
  the bound that a split w = uv gives on the class id lies above
  the cycle point of w exactly when c lies above the cycle point of
  vu; for 3c + 1 <= 2^L the split after the leading 1 gives the drop
  at c itself. Not cited in the text.
- Paper 2: its Lean table lists TCongruenceSplit, "all 144". Still
  33 pages.

## R_67 (20 October 2026)

- Paper 2: "Mike Winkler" in full on the title page and in the
  licence notice below it. Paper 1: its bibliography entry of paper
  2 names "Mike Winkler".
- Public: paper 2's PDF, and `src/` with the LaTeX sources of both
  papers and their `.ind` files.

## R_66 (20 October 2026): an audit round

An audit by nine independent readers, plus the build, the axioms of
every cited Lean name, the key terms and the labels. No wrong number,
table cell, figure datum or Lean statement was found in either paper.
The 25 findings were wording, stale comments and one incomplete
reference; all are fixed. Neither paper's mathematics changed.

- Paper 2, Rhin paragraph: "Lean's kernel checks that K = 1 and
  C = 2 suffice for every n <= 10^60 (`rhinBoundUpTo_one_two`)" in
  place of a stale bound of 20 000.
- Both papers quote the same bounds: the width identity checked for
  every Order up to ten million (paper 2: 10 781 273), and 47 as the
  tightest case below 20 000 000.
- Paper 2, Brackets: the sentence citing `lvlDrop_iff_isTDrop` says
  "under it for every start".
- Paper 2: three citations completed (`sbNode_inside`,
  `dropLast_mem_dyckSetQ`), and Thomas and Williams with volume and
  pages, Selecta Math. 24 (2018), 2003-2034.
- Smaller wording fixes in both papers, and comments in the Lean
  files (no statement or proof changed).

## R_65b and R_65c (19 October 2026)

- Lean: no change to any proof or statement. The README names the
  papers and files by their current names.

## R_65a (19 October 2026): first public release

- Paper 1 (PDF), `building.html`, `pv.py` and the Lean sources.
- Licences: MIT for code, CC BY 4.0 for text and figures.
