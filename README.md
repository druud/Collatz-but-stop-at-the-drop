# Collatz, but stop at the drop

Two papers, a draft of a third, and the Lean 4 / Mathlib formalization of their results.
The question studied is not whether every start reaches 1, but whether every
x > 1 eventually falls below itself: its *drop*.

Both papers are archived on Zenodo, each with its source files:
paper 1 at [doi:10.5281/zenodo.23631043](https://doi.org/10.5281/zenodo.23631043),
paper 2, with the Lean files, at [doi:10.5281/zenodo.23631546](https://doi.org/10.5281/zenodo.23631546)
(these DOIs always point to the newest version).
The first versions, of 25 October 2026 (R_75), are at
[doi:10.5281/zenodo.23631044](https://doi.org/10.5281/zenodo.23631044) (paper 1) and
[doi:10.5281/zenodo.23631547](https://doi.org/10.5281/zenodo.23631547) (paper 2);
their PDFs are here as the `_zenodo.pdf` files.

| File | What |
|---|---|
| `R_collatz_stop_at_the_drop_1.pdf` | Paper 1, *Now with less noise*: an introduction without proofs (Ruud H.G. van Tol); the next version after the one on Zenodo |
| `R_collatz_stop_at_the_drop_1_zenodo.pdf` | Paper 1 as on Zenodo |
| `R_collatz_stop_at_the_drop_2.pdf` | Paper 2, *A game with two letters: the proofs* (Ruud H.G. van Tol and Mike Winkler); the next version after the one on Zenodo |
| `R_collatz_stop_at_the_drop_2_zenodo.pdf` | Paper 2 as on Zenodo |
| `R_collatz_stop_at_the_drop_3.pdf` | Paper 3, a **draft** (marked with its version, e.g. "Draft: R_81"): what lies around the drop, in the language of the 3-smooth numbers; not archived, it may change (Ruud H.G. van Tol) |
| `R_collatz_stop_at_the_drop_best.pdf` | *The start words with the highest drop ratio*, a **draft** beside the series: the best of the Order, the class id whose drop falls the least (OEIS A402443), with the bests of Orders 1 to 378 and their certificates (Ruud H.G. van Tol); to be archived on Zenodo as an active document |
| `R_collatz_stop_at_the_drop_zeta.pdf` | *The drop zeta function*, a **draft** beside the series: the dynamical zeta function of the drop map, with the drop words in the role of the primes; its poles, and an identity for the number of drop words of each Order (OEIS A100982) from binomial coefficients alone (Ruud H.G. van Tol); not archived, it may change |
| `media/building.html` | the game of paper 1 in a browser: a building with stairs and poles, a rider to its drop; open it at [druud.github.io/Collatz-but-stop-at-the-drop/media/building.html](https://druud.github.io/Collatz-but-stop-at-the-drop/media/building.html) |
| `media/drop_tree.html` | the admissible words of Orders 1 to N as one tree (paper 3, Chapter 3), with the best class id of each Order drawn bold; options for the max Order, the best, the order at a split, shape and layout; open it from disk in a browser |
| `media/drop_turn.html` | the words of one Order (2 to 14) as turns around the unit circle, with the best, the smallest start, the word with its ones first and the wall word marked (the picture on the title page of the paper beside the series is its view `#6.s.lin.earn.marked`); options for the scaling, radius, angle and what is shown; the link carries the state; open it from disk in a browser |
| `pv.py` | the admissible words: counts, ranks, class ids, chains, record Orders and more; `./pv.py test` runs the self-test (Python 3.8 or later, no extra packages) |
| `CHANGES.md` | the changes since the first public release, newest first |
| `src/` | the LaTeX sources of the papers, with the index files of the first four (see below); `lean_files/`, the Lean sources, and `lean_files.zip`, the same as one file: unzip, then `lake exe cache get && lake build` in `lean_files/`; `best_of_order/`, the Lean package of the best of the Order (it uses `lean_files/` beside it; `lake build` there after `lean_files/`), with its scripts (`scripts/`) and the bests with their certificates (`data/`), and `best_of_order.zip`, the same as one file |

## Building the papers

In `src/`, run `pdflatex R_collatz_stop_at_the_drop_1.tex` three times, then the
same for `_2.tex`, then for `_3.tex` (and `_best.tex` and `_zeta.tex`, each on its own): paper 2 links into paper 1 through `xr-hyper` and
reads its `.aux`; paper 3 links into both.

## Licence

- Code (Lean, Python, scripts): MIT, see `LICENSE`.
- Text, figures and other documents (papers, `.md`, `.tex`, images): CC BY 4.0, see `LICENSE-CC-BY-4.0`.
