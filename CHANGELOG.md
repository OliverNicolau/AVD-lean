# Changelog

All notable changes to this formalization are recorded here.  Versions follow the `version`
field of `lakefile.toml`; released versions are tagged `vX.Y.Z`.

## 0.2.0 — unreleased

Planar-topology dependency replaced, and no `sorry` left.

* **Dependency.**  `schoenflies-lean` (Á. Begué) is dropped.  The planar topology is now
  taken from [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0), pinned at
  commit `4908b0344e1be5f7e9e5af7f7e640464843a2c84`.  The toolchain moves from
  `leanprover/lean4:v4.32.2` to `leanprover/lean4:v4.36.0-rc2`, and Mathlib from `v4.32.2` to
  commit `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, the one pinned by Tau Ceti.  The
  previous version is tagged `v1-schoenflies`.
* **Trust boundary.**  `AbstractVoronoi/Jordan/Backend.lean` is still the only file that
  imports the external library.  It proves from Tau Ceti and Mathlib the Jordan curve
  theorem (`jordan_curve_theorem`), the connectedness of the complement of a simple arc
  (`isConnected_compl_arc`, new), the Jordan–Schönflies theorem
  (`jordan_schoenflies_of_homeomorph`) and the two facts about the model square
  (`isJordanCurve_modelCurve`, `IsJordanCurve.nonempty_homeomorph_modelCurve`).  The plane is
  still `EuclideanSpace ℝ (Fin 2)`, identified with `ℂ` inside `Backend.lean`.
* **Proved here instead of imported.**  Arcs in open connected sets
  (`AVD.exists_isArc_of_isPreconnected`, and `AVD.exists_arc_in_open`, moved from
  `Adapter.lean`) and arcs avoiding a simple arc (`AVD.exists_isArc_compl_arc`), in the new
  file `AbstractVoronoi/Jordan/SimpleArcs.lean`; and the non-planarity of `K₃,₃`
  (`AVD.noPlaneEmbeddingK33`, `Jordan/K33.lean`), from the Jordan–Schönflies theorem and the
  θ-curve theorem.
* **Theorem 10.**  The single `sorry` is gone: `AVD.CurveSystem.theorem10` now takes Euler's
  inequality `AVD.EulerSphereInequality` as an explicit hypothesis `hEuler`.  The project
  contains no `sorry`, and every theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`.
* **Build.**  Tau Ceti has no prebuilt binaries usable here, so a first build compiles about
  360 of its files (about ten minutes on a 16-core laptop, longer on CI runners) before the
  project.

## 0.1.0 — first public version

The foundations of abstract Voronoi diagrams, following, statement by statement, the first
half of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
Computational Geometry 42 (2009) 885–902,
[doi:10.1016/j.comgeo.2009.03.002](https://doi.org/10.1016/j.comgeo.2009.03.002).

Formalized and proved (`AbstractVoronoi/Paper/`):

* **Definition 1** — systems of bisecting curves and the axioms `A₁`, `A₂`, `A₃`
  (`AVD.CurveSystem`, `AVD.CurveSystem.Admissible`); the formal notion of a curve system is
  slightly more general than the printed one — the two pieces `D(p,q)`, `D(q,p)` a curve cuts
  the plane into are only required to be open, disjoint, preconnected and complementary to
  the curve, while their non-emptiness, connectedness and unboundedness are *derived* from
  axiom `A₁` for admissible systems (`AVD.CurveSystem.D_nonempty`,
  `AVD.CurveSystem.D_isConnected`, `AVD.CurveSystem.D_not_isBounded`);
* **Definition 2** — Voronoi regions and the Voronoi diagram
  (`AVD.CurveSystem.voronoiRegion`, `AVD.CurveSystem.voronoiDiagram`);
* **Lemma 3** — the regions are open and the diagram is closed;
* **Theorem 4** — the structure of a neighbourhood of a point of a Jordan curve;
* **Lemma 5**, **Lemma 6**, **Lemma 7** (i) and (ii), **Lemma 8**, **Lemma 9**;
* **Theorem 10** — the diagram of `n` sites is a finite plane graph of size `O(n)`; every
  part of it is proved except the final count, which uses Euler's inequality.

Supporting plane topology (`AbstractVoronoi/Jordan/`): accessibility of the points of a
Jordan curve, crosscuts and θ-curves, small Jordan subdomains near a boundary point,
completion of an arc to a closed Jordan curve, the non-planarity of `K₃,₃`, and finite plane
graphs with their faces.  It is built on Mathlib and on Álvaro Begué's Lean 4 formalization
of the Jordan–Schönflies theorem.

Known limitation: `AVD.EulerSphereInequality` (`e + 1 ⩽ v + f` for finite plane graphs) is
stated but not proved, and the proof of Theorem 10 invokes it through the single `sorry` of
the project.  Everything else depends only on the standard axioms of Lean; see
`docs/formalization.md` and `notes/status-and-open-problems.md`.

Documentation: `README.md`, `docs/formalization.md`, `docs/library.md`,
`docs/publishing.md`, the blueprint in `blueprint/`, and the working notes in `notes/`.
