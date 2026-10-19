# Collatz, but stop at the drop

Two papers, and the Lean 4 / Mathlib formalization of their results.
The question studied is not whether every start reaches 1, but whether every
x > 1 eventually falls below itself: its *drop*.

| File | What |
|---|---|
| `R_collatz_stop_at_the_drop_1.pdf` | Part 1, *Now with less noise*: an introduction without proofs (Ruud H.G. van Tol) |
| `R_collatz_stop_at_the_drop_2.pdf` | Part 2, *A game with two letters: the proofs* (Ruud H.G. van Tol and M. Winkler) |
| `building.html` | the game of part 1 in a browser: a building with stairs and poles, a rider to its drop |
| `pv.py` | the admissible words: counts, ranks, class ids, chains, record Orders and more; `./pv.py test` runs the self-test (Python 3.8 or later, no extra packages) |
| `All_lean.zip` | the Lean sources; unzip, then `lake exe cache get && lake build` in `Lean/accelerated_collatz/` |

## Licence

- Code (Lean, Python, scripts): MIT, see `LICENSE`.
- Text, figures and other documents (papers, `.md`, `.tex`, images): CC BY 4.0, see `LICENSE-CC-BY-4.0`.
