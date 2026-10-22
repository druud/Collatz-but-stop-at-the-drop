# Collatz, but stop at the drop

Lean 4 / Mathlib formalization, with a Python companion, of the papers
*Collatz, but stop at the drop*: paper 1, *Now with less noise*, an
introduction without proofs (Ruud H.G. van Tol, with assistance from Claude,
Anthropic), and paper 2, *A game with two letters: the proofs* (Ruud H.G. van Tol
and Mike Winkler, with assistance from Claude, Anthropic, and ChatGPT, OpenAI).

The question studied is not whether every start reaches 1, but whether every
x > 1 eventually falls below itself: its *drop*. The two are equivalent
(`tDrop_equiv_collatzT` for the step T, `drop_equiv_collatz` for the fast map
R). Everything here looks at the way to the drop, never beyond it.

All results are proved without `sorry`. Two statements remain open and are
stated as definitions, not assumed: `Covering` and `WidthIdentity`
(Terras 1976, Conjecture 2.9), equivalent to `ClassDrops`. One published theorem
is stated the same way and used only as a hypothesis: `SweepBijective`
(Thomas, Williams 2018, Thm 6.3), for q = 3 and for the words of every
odd q >= 3 (the q-family of Winkler 2026). Rhin's (1987) lower bound on
2^p2(n) - 3^n enters the same way, as `RhinBound`.

## Contents

| Path | What |
|---|---|
| `AcceleratedCollatz/` | the Lean library (namespace `AcceleratedCollatz`) |
| `AcceleratedCollatz/DeadCode.lean` | unused declarations, not imported by the library |
| `AcceleratedCollatz/ChainDecomposition.lean` | self-contained extract (Mathlib only): chain decomposition, deficit budget, record lows, counts of A100982 |
| `AcceleratedCollatz/ChainQ.lean` | self-contained extract (Mathlib only): for the words of every odd q >= 3, the chain decomposition with its codes, count and deficit budget, the gaps of the record Orders, and the first word of each Order as a chain of first words |
| `AcceleratedCollatz/SmoothPlace.lean` | self-contained extract (Mathlib only): the place of p^a q^b among the numbers p^i q^j for any two bases p, q > 1 (Mintz 1981, Theorems 1 to 4), and for 2 and 3 the place of 2^a 3^b among the 3-smooth numbers |
| `AcceleratedCollatz/SmoothRuler.lean` | Mathlib only: the 3-smooth numbers on a plain ruler; the open statement `RulerGap` (between neighbours a < b no 3-smooth number lies after 2b - a and before b^2 / a), its form on exponents (`rulerGap_iff_ordersGap`), the reduction for bounded exponents (`rulerGapUpTo_of_ordersGapFrame`), and a rule that fails (`border_rule_fails`); the library imports it through `TRulerRecord`, which states its steps by the record Orders (`stepAt_two_three_iff`, `stepAt_three_two_iff`) and `RulerGap` over the record Orders only (`rulerGap_iff_records`, `rulerGapUpTo_of_records`), and `TRulerDeficit`, which states the gap condition as an inequality on deficits (`gapAt_two_three_iff_deficit`, `gapAt_three_two_iff_deficit`), the timing of a step as ending at the next record Order (`upperTiming_at_iff_next`, `lowerTiming_at_iff_next`) and `RulerGap` as the two deficit conditions (`rulerGap_iff_deficit`), and `TRulerPair`, which states `RulerGap` as one deficit inequality per pair of neighbouring record Orders, at the largest record Order c ≤ b + b' (upper) or c < P + P' (lower) (`rulerGap_iff_pairs`), and `TRulerCheck`, which checks those inequalities for every pair up to 10^60 by a kernel walk (`rulerPairs_upTo`) and so gives the ruler gap for every exponent of 2 and every exponent of 3 up to 10^59 (`rulerGapUpTo_ten_pow`) |
| `AcceleratedCollatz/SweepQ.lean` | self-contained extract (Mathlib only): the sweep map on the admissible words of every odd q >= 3, with its start variant (upper record Orders) and its cut variant (lower record Orders) |
| `pv.py` | virtual cache of admissible words: counts, ranks, class ids, chains, excess/gap, record Orders, first words, sweeps, bracket words, the 3-smooth numbers in order; `./pv.py test` runs the self-test |
| `building.html` | the game of paper 1 in a browser: a building with stairs and poles, a rider to its drop |
| `R_collatz_stop_at_the_drop_1.tex`, `_2.tex` | the two papers (`pdflatex`; build paper 1 first, paper 2 links to it) |

## Build

```sh
lake exe cache get      # Mathlib binaries
lake build              # every file under AcceleratedCollatz/
```

`TFiniteCheck` lets the kernel compare numbers of about 1.7·10^7 bits, so every `lean` that
compiles it needs `LEAN_NAT_MAX_SIZE` of at least 300000000 (Lean 4.33.1 or later). For
`lake build` the target `natMaxSize` of `lakefile.lean` sets it to 1000000000 in Lake's own
process when it is unset; `lake env lean` and the editor's Lean server need it in the
environment, else `TFiniteCheck` stops with that message. The Lean toolchain is pinned in
`lean-toolchain`; the Mathlib version in `lakefile.lean`. `lake build` builds every file under
`AcceleratedCollatz/` (the `globs` of `lakefile.lean`), so also `DeadCode.lean` and the
extracts `ChainDecomposition.lean`, `ChainQ.lean`, `SmoothPlace.lean` and `SweepQ.lean`, which
the library does not import and which build in any Mathlib project; `SmoothRuler.lean` builds
there too.

`pv.py` needs Python 3.8 or later and no extra packages:

```sh
./pv.py list 5          # the 7 admissible words of Order 5
./pv.py count 20 40     # A100982(20), A100982(40)
./pv.py attrs 1101      # class id 11, drop 10, rho 23, chain
./pv.py maxq 1 2 3 4 5  # class id closest to its cycle point, per Order
```

## Map of the library

Grouped by the chapters of paper 2, each module with the chapter it belongs to.

| Chapter | Modules | Main results |
|---|---|---|
| 1 Only go all the way down if needed | `DescendToMinimum`, `DropEquivalence`, `DropEquivalenceT` | `drop_equiv_collatz`, `tDrop_equiv_collatzT` |
| 2 Words and levels | `AdmissibleLength`, `TStaircase`, `TParity`, `TActive`, `TPrefixCount`, `TRank` | `admissible_length`, `admissible_not_prefix`, `admissible_iff_steps`, `card_admSet_add_active`, `card_admSet_eq_count`, `rowStep_eq_rowStepFast`, `admIndex_eq_unrank`, `admIndex_symm_eq_rank` |
| 3 From words to numbers: the cycle point | `TCorrespondence`, `TAffine`, `TDrop`, `TClass`, `TSieve`, `TRhoLower`, `TCongruenceSplit` | `classEquiv`, `affine_classId`, `drop_iff_rho`, `fixed_iff_rho`, `rho_pos_iff`, `split_bound_iff`, `split_one_iff` |
| 4 The chain decomposition | `TSplit`, `TSplitGrammar`, `TChain`, `TChainOrders`, `TBudget`, `TRecordLow`, `TFirstWord`, `TFirstWordQ`, `TFirstOrders`, `TNest`, `TBracket`, `TBracketDrop`, `TBracketDyck`, `TBracketChain`, `TBracketTree`, `TBracketParse`, `TBracketDecode`, `TBracketCount`, `TChainEquiv`, `TChainParse`, `TAttrs`, `TSweep`, `TSweepPerm`, `TStartSweep`, `TGridOrder`, `TBlockRecord`, `TWordQ`, `TSweepQ`, `TSweepZ`, `TSweepPermQ`, `TGridOrderQ`, `TBlockRecordQ`, `TStartSweepQ`, `TStartSweepPermQ`, `TStartSweepInjQ`, `TCutSweepQ`, `TRecordGapQ`, `TSmoothNext`, `TSmoothBetween`, `TSmoothNextQ`, `TLastRecordsQ`, `TSmoothClass`, `TSmoothClassQ`, `TSmoothPlace`, `TSmoothPlaceQ`, `TSternBrocot`, `TSternBrocotQ`, `TSternBrocotConv`, `TSternBrocotConvQ`, `TSmoothSucc`, `TSmoothSuccQ`, `TFloorSum`, `TBisect`, `TRecordFloor`, `TRecordWalk`, `TSmoothRank`, `TSmoothProgram`, `TSmoothProgramConv`, `TSternBrocotCert`, `TSplitQ`, `TChainQ`, `TRecordLowQ`, `TFirstChainQ`, `TFirstOrdersQ`, `TFirstGreedy`, `TFirstGreedyQ`, `TChainEquivQ`, `TCountQ`, `TBudgetQ`, `TBracketQ`, `TBracketDyckQ`, `TBracketChainQ`, `TBracketTreeQ`, `TBracketParseQ`, `TBracketDecodeQ`, `TBracketWordTreeQ`, `TBracketOneQ`, `TBracketClashQ` | `exists_chain`, `chain_unique`, `admissible_iff_chain`, `chainEquiv`, `codeEquiv`, `chainEquiv_eq_chainOf`, `codeEquiv_eq_codeOf`, `classIdC_eq`, `keyPV_core`, `attrs_drop`, `validOrders_iff_dropLast`, `exists_chain_recordLow`, `unrank_zero`, `isRecordLow_firstWord`, `firstWord_chain`, `upperRecord_order_of_firstWord`, `upperRecord_sub_of_lowerRecord`, `lowerRecord_sub_of_upperRecord`, `smooth_next`, `upperRecord_iff_none_between`, `blockFactor_mul_mod_lt`, `smooth_class_mul_mod_lt`, `card_smoothBelow`, `card_smoothBelowAt`, `latticePlace_eq`, `bracketWord_injective`, `lvlDrop_iff_isTDrop` (under `WidthIdentity`), `sum_bracketWord`, `bracketWord_chain`, `image_bracketWord_admSet`, `isBracketTree_iff`, `invOn_bracketDecode`, `ncard_isBracketTree`, `sweep_mem_admSet`, `sweep_bijOn` (under `SweepBijective`), `mapsTo_startSweep_iff`, `startSweep_bijOn_iff` (under `SweepBijective`), `startSweep_injOn` (under `SweepBijective`), `cutSweep_mem_admSet`, `cutSweep_bijOn_iff` (under `SweepBijective`), `not_injOn_cutSweep`, `gridLinear_iff_upperRecord`, `upperRecord_iff_blockFactor`, `sweepQ_mem_admSetQ`, `sweepQ_bijOn` (under `SweepBijective`), `gridLinearQ_iff_upperRecordQ`, `upperRecordQ_iff_blockFactorQ`, `upperRecord_iff_sbWalk`, `lowerRecord_iff_sbWalk`, `upperRecordQ_iff_sbWalkQ`, `upperRecord_iff_semiconv`, `lowerRecord_iff_semiconv`, `log2_three_convs`, `smooth_succ`, `floorSum_eq`, `div_record_add_one`, `div_record_swap_add_one`, `recordWalk_spec`, `classCount_eq`, `smoothJI_spec`, `latticeOrd_smoothJI_conv`, `exists_sbCert`, `latticeOrd_smoothJIFind`, `firstWord_eq_greedy`, `admissibleQ_iff_exists_chainQ`, `splitQ_unique`, `isRecordLowQ_iff_cut`, `firstWordQ_le`, `firstWordQ_blocks`, `firstWordQ_chain`, `upperRecordQ_order_of_firstWordQ`, `chainEquivQ`, `codeEquivQ`, `card_admSetQ_succ`, `levelUpQ_iff_budgetQ`, `bracketWordQ_injective`, `sum_bracketWordQ`, `bracketWordQ_chainWordQ`, `lvlDropQ_zero_iff_cut`, `word_bijOn_validTreesQ`, `ncard_validTreesQ`, `parseTreeQ_eq_some_iff`, `isTreeWordQ_iff`, `validQ_iff`, `decodeQ_encQ`, `encQ_node_eq`, `bracketWordQ_word_eq_encQ`, `decodeQ_bracketWordQ`, `bracketWordOneQ_chain`, `not_injOn_bracketWordOneQ` |
| 5 Counting the words | `TAdmSet`, `TCount`, `TBinomial`, `TBinomialRange`, `TPersistent` | `card_admSet_succ`, `choose_eq_sum_admSet`, `choose_eq_sum_admSet_of_le`, `card_persSet` |
| 6 The fast map and sorting | `RMap`, `RShift`, `Core`, `MarkedVector`, `MarkedVectorShift`, `OrderPreservation`, `Tree`, `TLex`, `TVectorLex`, `TEncode`, `TBridge`, `TFold`, `TRLink`, `TMarkerPoint`, `TMarkerPointHigh`, `TMarkerTree`, `TWordPoint`, `TSternBrocotTree`, `TSternBrocotInterval`, `TSternBrocotOnto`, `TUds`, `TUdsDrop`, `TUdsCount` | `order_preservation`, `lex_enumeration`, `tBits_lt_iff_markedVector_lt`, `markerPoint_ht`, `hiPoint_runs`, `aytPoint_complement`, `hcsPoint_complement`, `sbPoint_runs`, `sbPoint_lt_iff_lt`, `sbPoint_eq_sbMed`, `admissible_interval_le`, `admissible_touch_iff`, `existsUnique_sbPoint_eq`, `existsUnique_class_point`, `exists_admissible_between`, `isUdsStop_iff_of_large`, `udsWord_class`, `le_order_of_isUdsStop`, `card_udsStopSet` |
| 7 What is still open | `TWidth`, `TCovering`, `TTerras`, `DropTermination`, `TRhoBound`, `TRhoMax`, `TRhoMaxBound`, `TRhoMaxCheck`, `TRhoMaxRecord`, `TRhoSlack`, `TWidthBound`, `TWidthRecord`, `TFiniteCheck`, `TRulerRecord`, `TRulerDeficit`, `TRulerPair`, `TRulerCheck`, `TRhinBound`, `TRhinCheck`, `TRhinLog`, `TCycle`, `TMersenne`, `TMod4`, `TGMap` | `widthIdentity_iff_classDrops`, `dropConjecture_iff_acc`, `drops_of_covering_width`, `covering_of_drops`, `terras_density`, `three_pow_le_rho_add`, `rho_add_eq_three_pow_iff` (both in `TRhoLower`, row 3), `rho_le_rhoMax`, `rho_eq_rhoMax_iff`, `rhoMax_slack`, `lowerRecord_iff_slackTerm`, `classDrops_iff_small`, `classDropsAt_of_verified`, `classDrops_iff_small_rhoMax`, `classDropsAt_of_verifiedMax`, `upperRecord_iff_rmax`, `upperRecord_iff_widthBoundMax`, `classDropsAt_of_verifiedMax_record`, `rhinBoundUpTo_one_two`, `upperRecord_iff_widthBound`, `classDropsAt_of_verified_record`, `classDropsAt_le_10781273`, `classDrops_of_rhinBound`, `rhinBound_of_rhinLog`, `exists_rhinBound_of_rhinLogFrom`, `no_cycle_of_widthIdentity`, `order_mersenne_succ_le`, `classId_mod4`, `gStep_spec`, `gStep_formula`, `gChain_drop_iff`, `rulerGap_iff_records`, `rulerGap_iff_deficit`, `rulerGap_iff_pairs`, `rulerGapUpTo_ten_pow` |
| (shared) | `Numlib` | general number theory |

## OEIS

The papers connect these sequences: A000265, A003586, A014682, A020914, A022921, A056576,
A060412, A076227, A100982, A122442, A177789, A186008, A206788, A243115,
A260591, A324245, A349414, A350082, A368514, A375782, A375961, A387325. The G-step counts of `TGMap` are A400742.

## Acknowledgements

M. Winkler (Ruhr University Bochum) for the range form of the binomial
identity, the deficit-budget formulation, a careful review of the chain
decomposition, and the question that led to the sweep for every odd q.
A. Wechsler for his reading of paper 1.
