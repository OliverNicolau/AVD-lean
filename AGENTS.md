# Notes for contributors and automated tools

This file collects the conventions of the repository and the checks that must pass.  It is
written for whoever — human or automated assistant — edits the Lean sources.  The
human-facing documentation is `README.md`, `docs/formalization.md` and `docs/library.md`.

## What this repository is

A formalization in Lean 4 + Mathlib of Definition 1 – Theorem 10 of R. Klein, E. Langetepe,
Z. Nilforoushan, *Abstract Voronoi diagrams revisited*, Computational Geometry 42 (2009)
885–902.  No new mathematics is claimed: every numbered statement is the one printed in the
paper, and the proofs follow the arguments of the paper.  The supporting material in
`AbstractVoronoi/Jordan/` is classical plane topology that the paper uses freely and that
Mathlib does not contain.

`AbstractVoronoi/Paper.lean` and `AbstractVoronoi/AVD/` are written as a library:
intermediate facts are stated as named, reusable lemmas rather than inlined in proofs.

## Checks

```
lake exe cache get                      # Mathlib binaries; strongly recommended
lake build                              # builds everything; one `sorry`, in Theorem 10
lake exe runLinter AbstractVoronoi.All  # the Mathlib declaration linters, all passing
lake env lean scripts/axioms.lean       # the axioms each numbered statement depends on
```

The build must stay free of errors and of warnings, save the one
`declaration uses 'sorry'` warning for Theorem 10.  The library is built with the same Lean
options as Mathlib — no automatic implicit arguments, the standard Mathlib style linter set;
see `lakefile.toml`.

`scripts/axioms.lean` prints, for every numbered statement, the axioms its proof uses:
`propext`, `Classical.choice` and `Quot.sound` for all of them, and `sorryAx` in addition for
`AVD.CurveSystem.theorem10` alone.

Continuous integration (`.github/workflows/lean.yml`) runs the build and the linter, and
fails if a second `sorry` appears in `AbstractVoronoi/`.

## Invariants to preserve

* **Exactly one `sorry`**, in `AbstractVoronoi/Paper/Theorem10.lean`, standing for Euler's
  inequality `AVD.EulerSphereInequality`.  Never add another, and never add an `axiom`
  declaration: an unproved statement is stated as a `Prop`-valued definition or a
  hypothesis, as `AVD.EulerSphereInequality` is.
* **Docstrings quote the paper.**  Every declaration in `AbstractVoronoi/Paper/` carries a
  docstring naming and quoting the statement of the paper it formalizes, and saying
  explicitly where the formal statement differs from the printed one.  All declarations of
  the project are documented.
* **Statements stay faithful.**  Any deviation from the printed statement must be recorded
  both in the docstring and in `notes/statement-check.md`, and summarised in
  `docs/formalization.md`.
* **Pinning.**  `lean-toolchain` and `lake-manifest.json` pin the compiler, Mathlib, the
  Jordan–Schönflies dependency and all transitive dependencies.  Do **not** run
  `lake update`: it would move the dependencies off the revisions the library is checked
  against.  If the manifest is ever out of sync with `lakefile.toml`, regenerate it and
  check that it still pins Mathlib at the revision of the `v4.32.2` tag
  (`905b95818eb32af7874a58b427f50c1711a5e96c`), matching `lean-toolchain`, and
  `schoenflies-lean` at `05a43d29cde026618777db3d4e4316204ccca237`; then rebuild the whole
  library against it.
* **Style.**  Lines are wrapped at 100 characters; Mathlib naming conventions are used.

## After changing a statement

Re-run `python3 blueprint/generate.py`, which extracts from `AbstractVoronoi/Paper/` the
docstring and the Lean statement of each numbered item and rewrites `blueprint/blueprint.tex`
and `blueprint/blueprint.md`; recompile the PDF with `tectonic blueprint/blueprint.tex`
(XeLaTeX also works).  Then update `notes/statement-check.md` and `docs/formalization.md`.

## The working notes

`notes/` holds the material that is too detailed for the documentation:

* `statement-check.md` — the statement-by-statement comparison with the paper;
* `Lemma8-figures-and-plan.md` — Figs. 5–8 of the paper and how each configuration of the
  proof of Lemma 8 is handled;
* `euler-formula-and-counting.md` — what the `O(n)` count needs from Euler's formula, and
  why the existing Lean formalizations of Euler's formula do not supply it;
* `status-and-open-problems.md` — what is proved, what is open, and the natural
  continuations;
* `aristotle-session-log.md` — the log of the formalization sessions that produced the
  library, kept for provenance only.

## Publication

`docs/publishing.md` lists what is left to do on the GitHub side: filling in the address of
the repository with `scripts/set-repository-url.sh`, the description, topics and Pages
settings, tagging a release, and what is quoted from the paper.  `CHANGELOG.md` records what
each released version contains.

`docbuild/` is an auxiliary Lake package that generates the HTML API documentation with
`doc-gen4`; it is deliberately separate, so that an ordinary `lake build` does not download
the generator.  The `Documentation` workflow (`.github/workflows/docs.yml`) runs it and
publishes the result to GitHub Pages.
