/-
The axiom audit of the project.  Run it with

```
lake env lean scripts/axioms.lean
```

after `lake build`.  It prints the axioms on which the formal counterpart of each numbered
statement of

  R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

depends.  The expected output is `propext, Classical.choice, Quot.sound` — the standard
axioms of Lean — for every statement, Theorem 10 included: the one statement the project
leaves unproved, Euler's inequality `AVD.EulerSphereInequality` for finite plane graphs, is
an explicit hypothesis of Theorem 10, not a `sorry`.

This file is not part of the library: it is not under `AbstractVoronoi/`, so `lake build`
does not compile it.
-/
import AbstractVoronoi.Paper

-- Definition 1 and Definition 2.
#print axioms AVD.CurveSystem
#print axioms AVD.CurveSystem.Admissible
#print axioms AVD.CurveSystem.VR
#print axioms AVD.CurveSystem.V
#print axioms AVD.CurveSystem.voronoiRegion
#print axioms AVD.CurveSystem.voronoiDiagram

-- Lemma 3 to Lemma 9.
#print axioms AVD.CurveSystem.lemma3
#print axioms AVD.JordanCurveAccessibility
#print axioms AVD.theorem4
#print axioms AVD.CurveSystem.lemma5
#print axioms AVD.CurveSystem.lemma6
#print axioms AVD.CurveSystem.lemma7_touching
#print axioms AVD.CurveSystem.lemma7_crossing
#print axioms AVD.CurveSystem.lemma8
#print axioms AVD.CurveSystem.lemma9

-- Theorem 10: the only declaration of the project depending on `sorryAx`.
#print axioms AVD.CurveSystem.theorem10

-- The ingredients of Theorem 10 that are proved.
#print axioms AVD.CurveSystem.isFinitePlaneGraph
#print axioms AVD.CurveSystem.three_le_edges_at_vertex
#print axioms AVD.CurveSystem.three_le_faces_at_vertex
#print axioms AVD.CurveSystem.vertexSet_ncard_le
#print axioms AVD.CurveSystem.edgeSet_ncard_le
#print axioms AVD.IsFinitePlaneGraph.ncard_le_of_degree
