# Collatz, but stop at the drop

Two papers, a draft of a third, and the Lean 4 / Mathlib formalization of their results.
The question studied is not whether every start reaches 1, but whether every
x > 1 eventually falls below itself: its *drop*.

Both papers are archived on Zenodo, each with its source files:
paper 1 at [doi:10.5281/zenodo.23631043](https://doi.org/10.5281/zenodo.23631043),
paper 2, with the Lean files, at [doi:10.5281/zenodo.23631546](https://doi.org/10.5281/zenodo.23631546)
(these DOIs always point to the newest version).

| File | What |
|---|---|
| `R_collatz_stop_at_the_drop_1.pdf` | Paper 1, *Now with less noise*: an introduction without proofs (Ruud H.G. van Tol) |
| `R_collatz_stop_at_the_drop_2.pdf` | Paper 2, *A game with two letters: the proofs* (Ruud H.G. van Tol and Mike Winkler) |
| `R_collatz_stop_at_the_drop_3.pdf` | Paper 3, a **draft** (marked with its version, e.g. "Draft: R_81"): what lies around the drop, in the language of the 3-smooth numbers; not archived, it may change (Ruud H.G. van Tol) |
| `building.html` | the game of paper 1 in a browser: a building with stairs and poles, a rider to its drop; open it at [druud.github.io/Collatz-but-stop-at-the-drop/building.html](https://druud.github.io/Collatz-but-stop-at-the-drop/building.html) |
| `pv.py` | the admissible words: counts, ranks, class ids, chains, record Orders and more; `./pv.py test` runs the self-test (Python 3.8 or later, no extra packages) |
| `CHANGES.md` | the changes since the first public release, newest first |
| `src/` | the LaTeX sources of the three papers with their index files (see below); `lean_files/`, the Lean sources, and `lean_files.zip`, the same as one file: unzip, then `lake exe cache get && lake build` in `lean_files/` |

## Building the papers

In `src/`, run `pdflatex R_collatz_stop_at_the_drop_1.tex` three times, then the
same for `_2.tex`, then for `_3.tex`: paper 2 links into paper 1 through `xr-hyper` and
reads its `.aux`; paper 3 links into both.

## Licence

- Code (Lean, Python, scripts): MIT, see `LICENSE`.
- Text, figures and other documents (papers, `.md`, `.tex`, images): CC BY 4.0, see `LICENSE-CC-BY-4.0`.
