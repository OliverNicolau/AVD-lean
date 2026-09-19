# Changelog

All notable changes to this formalization are recorded here.  Versions follow the `version`
field of `lakefile.toml`; released versions are tagged `vX.Y.Z`.

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
