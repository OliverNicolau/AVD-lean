import AbstractVoronoi.Paper.Definitions
import AbstractVoronoi.Paper.Theorem4
import AbstractVoronoi.Paper.Lemma3
import AbstractVoronoi.Paper.Lemma5
import AbstractVoronoi.Paper.Lemma6
import AbstractVoronoi.Paper.Lemma7
import AbstractVoronoi.Paper.Lemma8
import AbstractVoronoi.Paper.Lemma9
import AbstractVoronoi.Paper.Theorem10

/-!
# The statements of the paper

This module is the entry point for reading the formalization: it imports, and nothing else,
the files that contain the formal counterparts of the numbered statements of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

| statement of the paper | Lean declaration | file |
| --- | --- | --- |
| Definition 1 | `AVD.CurveSystem`, `AVD.CurveSystem.Admissible` | `Paper/Definitions.lean` |
| Definition 2 | `AVD.CurveSystem.voronoiRegion`, `…voronoiDiagram` | `Paper/Definitions.lean` |
| Lemma 3 | `AVD.CurveSystem.lemma3` | `Paper/Lemma3.lean` |
| Theorem 4 | `AVD.JordanCurveAccessibility`, `AVD.theorem4` | `Paper/Theorem4.lean` |
| Lemma 5 | `AVD.CurveSystem.lemma5` | `Paper/Lemma5.lean` |
| Lemma 6 | `AVD.CurveSystem.lemma6` | `Paper/Lemma6.lean` |
| Lemma 7 (i), (ii) | `AVD.CurveSystem.lemma7_touching`, `…lemma7_crossing` | `Paper/Lemma7.lean` |
| Lemma 8 | `AVD.CurveSystem.lemma8` | `Paper/Lemma8.lean` |
| Lemma 9 | `AVD.CurveSystem.lemma9` | `Paper/Lemma9.lean` |
| Theorem 10 | `AVD.CurveSystem.theorem10` | `Paper/Theorem10.lean` |

Everything else in the project is supporting material: `AbstractVoronoi/Jordan/` contains the
planar topology (the Jordan curve theorem and what is built on top of it), and
`AbstractVoronoi/AVD/` the API about systems of bisecting curves.

Every statement of the development is proved except one, inside the proof of **Theorem 10**,
which is the only declaration of the project whose proof contains a `sorry`: **Euler's
inequality** `e + 1 ⩽ v + f` for finite plane graphs (`AVD.EulerSphereInequality`, stated in
`AbstractVoronoi/Jordan/PlaneGraph.lean`), the classical fact from which the paper reads off
the count `O(n)`.

The other input of that count, the **degree condition** at a Voronoi vertex — at least three
edges end at it — is proved (`AVD.CurveSystem.three_le_edges_at_vertex`,
`AbstractVoronoi/AVD/VertexDegree.lean`), and so is the counting that turns the two into the
bounds the paper uses (`AVD.IsFinitePlaneGraph.ncard_le_of_degree`, via the handshake
inequality).
Everything else Theorem 10 asserts is proved, and Definition 1 to Lemma 9 depend only on the
standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`).  The only external
input is the Lean 4 formalization of the Jordan–Schönflies theorem this project depends on;
see `AbstractVoronoi/Imports.lean`.
-/
