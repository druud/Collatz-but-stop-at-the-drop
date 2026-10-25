# Changes

The changes to this repository since its first public release, newest
first. Version names (R_65a, R_66, ...) are the authors' own labels.

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
  of on the title page. 34 pages (was 33).

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
