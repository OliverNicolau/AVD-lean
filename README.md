This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Abstract Voronoi diagrams, formalized in Lean 4

[![Build](https://github.com/OliverNicolau/AVD-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/OliverNicolau/AVD-lean/actions/workflows/lean.yml)

A machine-checked version of the foundations of **abstract Voronoi diagrams**: the axioms of
a system of bisecting curves, the Voronoi regions and the Voronoi diagram they define, and
the proof that the diagram of `n` sites is a finite plane graph of size `O(n)`.

Everything here follows, statement by statement, the first half of

> R. Klein, E. Langetepe, Z. Nilforoushan, **Abstract Voronoi diagrams revisited**,
> *Computational Geometry* **42** (2009) 885–902,
> [doi:10.1016/j.comgeo.2009.03.002](https://doi.org/10.1016/j.comgeo.2009.03.002)
> ([publisher's page](https://www.sciencedirect.com/science/article/pii/S0925772109000364);
> the article is not open access, so reading it may require a subscription),

namely Definition 1 – Theorem 10.  Each Lean declaration quotes the printed statement it
formalizes in its docstring.  This is a formalization of existing mathematics: the theorems
and their proofs are the authors', no new mathematical result is claimed.

| paper | Lean | status |
| --- | --- | --- |
| Definition 1 (axioms `A₁`, `A₂`, `A₃`) | `AVD.CurveSystem`, `AVD.CurveSystem.Admissible` | ✅ |
| Definition 2 (Voronoi region, Voronoi diagram) | `AVD.CurveSystem.voronoiRegion`, `…voronoiDiagram` | ✅ |
| Lemma 3 (regions are open, diagram is closed) | `AVD.CurveSystem.lemma3` | ✅ |
| Theorem 4 (structure of a Jordan curve neighbourhood) | `AVD.theorem4` | ✅ |
| Lemma 5 | `AVD.CurveSystem.lemma5` | ✅ |
| Lemma 6 | `AVD.CurveSystem.lemma6` | ✅ |
| Lemma 7 (i), (ii) | `AVD.CurveSystem.lemma7_touching`, `…lemma7_crossing` | ✅ |
| Lemma 8 | `AVD.CurveSystem.lemma8` | ✅ |
| Lemma 9 (`O(n³)` vertices) | `AVD.CurveSystem.lemma9` | ✅ |
| Theorem 10 (the diagram is a plane graph of size `O(n)`) | `AVD.CurveSystem.theorem10` | ⚠️ takes one classical fact as a hypothesis |

⚠️ **One classical fact is assumed, in one place.** Euler's inequality `e + 1 ⩽ v + f` for
plane graphs (`AVD.EulerSphereInequality`) is stated but not proved here — Mathlib does not
have it in a usable form — and Theorem 10 takes it as an explicit hypothesis `hEuler`.  The
project contains no `sorry`: everything, including all of Definition 1 – Lemma 9 and the
plane graph structure of the diagram, is proved from the standard axioms of Lean.  See
[`docs/formalization.md`](docs/formalization.md#what-is-proved-and-what-is-assumed).

## Using it as a dependency

Add to your `lakefile.toml`

```toml
[[require]]
name = "AbstractVoronoi"
git = "https://github.com/OliverNicolau/AVD-lean.git"
rev = "v0.2.0"   # or "main" to follow the default branch
```

(The repository address is filled in at publication time; `scripts/set-repository-url.sh`
does it in every file at once.)

and import

```lean
import AbstractVoronoi.Paper   -- the numbered statements of the paper
import AbstractVoronoi.All     -- everything, including the planar topology
```

Your project must use the toolchain of `lean-toolchain` (Lean `v4.36.0-rc2`) and the Mathlib
revision of `lake-manifest.json` (commit `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, the one
pinned by Tau Ceti).

Besides abstract Voronoi diagrams, the library contains a self-contained development of
**planar topology** (`AbstractVoronoi/Jordan/`) that may be useful on its own: accessibility
of the points of a Jordan curve, the crosscut and θ-curve theorems, small Jordan subdomains
near a boundary point, completion of an arc to a closed Jordan curve, the non-planarity of
`K₃,₃`, and finite plane graphs with their faces.

## Building it

With [`elan`](https://github.com/leanprover/elan) installed:

```
lake exe cache get   # Mathlib binaries; strongly recommended
lake build           # the whole library, with no `sorry`
```

Tau Ceti has no prebuilt binaries usable here, so a first build also compiles about 360 of
its files (about ten minutes on a 16-core laptop, longer on CI runners) before the project
itself.  All dependencies are pinned by `lean-toolchain` and `lake-manifest.json`, so a plain
`lake build` resolves nothing by itself; **do not run `lake update`**.  The same build runs
in CI (`.github/workflows/lean.yml`).

## Where to go next

* [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf) — every numbered statement of the
  paper next to the Lean statement that formalizes it (also as
  [`blueprint.md`](blueprint/blueprint.md)).
* [`docs/formalization.md`](docs/formalization.md) — how the paper is mapped into Lean, the
  four places where the formal statement differs from the printed one, and exactly what is
  proved and what is assumed.
* [`docs/library.md`](docs/library.md) — the layout of the library, file by file, and the
  planar-topology dependency it builds on.
* [`notes/`](notes) — working notes: a statement-by-statement check against the paper, the
  figures of Lemma 8, the Euler count, and the open problems.
* [`AGENTS.md`](AGENTS.md) — conventions and the checks to run, for contributors and for
  automated tools.
* **API documentation** — browsable HTML generated from the docstrings by
  [`doc-gen4`](https://github.com/leanprover/doc-gen4).  The `Documentation` workflow
  (`.github/workflows/docs.yml`) builds it from `docbuild/` and publishes it to GitHub
  Pages; see [`docs/publishing.md`](docs/publishing.md) for how to switch it on.
* [`CHANGELOG.md`](CHANGELOG.md) — what each released version contains.

## Citing

If you use this library, please cite **the paper** (the mathematics is theirs) and, if you
wish, this formalization; see [`CITATION.cff`](CITATION.cff).  The paper is published by
Elsevier and is not redistributed here: only its statements are quoted, in the docstrings,
and the DOI above resolves to the publisher's page.

The Lean sources were written by [Aristotle](https://aristotle.harmonic.fun).  To credit it,
tag @Aristotle-Harmonic on GitHub PRs/issues, or add it as a commit co-author:

```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

## Licence and acknowledgements

This repository is released under the **Apache License 2.0** (see [`LICENSE`](LICENSE)), the
licence of Lean 4, Mathlib and the other dependencies.

It builds on [Lean 4](https://github.com/leanprover/lean4),
[Mathlib](https://github.com/leanprover-community/mathlib4), and
[Tau Ceti](https://github.com/TauCetiProject/TauCeti), which supplies the Jordan curve
theorem, the Jordan–Schönflies theorem and the fact that a simple arc does not separate the
plane.  Version 0.1.0 was built instead on Álvaro Begué's Lean 4 formalization of the
Jordan–Schönflies theorem
([`schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean)); the sup-norm helpers
of `AbstractVoronoi/Jordan/SupNorm.lean` are adapted from it.  Full credits are in
[`docs/library.md`](docs/library.md#acknowledgements-and-dependencies).
