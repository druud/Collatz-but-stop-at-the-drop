# Changes

The changes to this repository since its first public release, newest
first. Version names (R_65a, R_66, ...) are the authors' own labels.

## Since R_78

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
