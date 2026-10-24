# Collatz, but stop at the drop

Two papers and the Lean 4 / Mathlib formalization of their results.
The question studied is not whether every start reaches 1, but whether every
x > 1 eventually falls below itself: its *drop*.

| File | What |
|---|---|
| `R_collatz_stop_at_the_drop_1.pdf` | Paper 1, *Now with less noise*: an introduction without proofs (Ruud H.G. van Tol) |
| `R_collatz_stop_at_the_drop_2.pdf` | Paper 2, *A game with two letters: the proofs* (Ruud H.G. van Tol and Mike Winkler) |
| `building.html` | the game of paper 1 in a browser: a building with stairs and poles, a rider to its drop; open it at [druud.github.io/Collatz-but-stop-at-the-drop/building.html](https://druud.github.io/Collatz-but-stop-at-the-drop/building.html) |
| `pv.py` | the admissible words: counts, ranks, class ids, chains, record Orders and more; `./pv.py test` runs the self-test (Python 3.8 or later, no extra packages) |
| `src/` | the LaTeX sources of both papers with their index files (see below); `lean_files/`, the Lean sources, and `lean_files.zip`, the same as one file: unzip, then `lake exe cache get && lake build` in `lean_files/` |

## Building the papers

In `src/`, run `pdflatex R_collatz_stop_at_the_drop_1.tex` three times, then the
same for `_2.tex`: paper 2 links into paper 1 through `xr-hyper` and reads its `.aux`.

## Licence

- Code (Lean, Python, scripts): MIT, see `LICENSE`.
- Text, figures and other documents (papers, `.md`, `.tex`, images): CC BY 4.0, see `LICENSE-CC-BY-4.0`.
