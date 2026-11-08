# Status of the project, and the problems it leaves open

This note records what is proved, what is left open, and what would be the natural
continuations of the development.  The statement-by-statement comparison with the printed
paper is in `statement-check.md`; the discussion of the Euler count is in
`euler-formula-and-counting.md`.

## 1. What is proved

Definition 1, Definition 2, Lemma 3, Theorem 4, Lemma 5, Lemma 6, Lemma 7 (i) and (ii),
Lemma 8 and Lemma 9 of

> R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
> Computational Geometry 42 (2009) 885–902

are formalized and proved, and so is Theorem 10, with Euler's inequality as an explicit
hypothesis `hEuler` for its `O(n)` count.  The project contains no `sorry`.  Every theorem
depends only on the standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`) on
top of the planar topology that `AbstractVoronoi/Jordan/Backend.lean` proves from Tau Ceti
and Mathlib; this can be reproduced with

```
lake build
lake env lean scripts/axioms.lean
lake exe runLinter AbstractVoronoi.All
```

The planar topology that the paper uses freely and that Mathlib does not contain is proved
in `AbstractVoronoi/Jordan/`: the global and local forms of Theorem 4, the accessibility of
the points of a Jordan curve, the crosscut and θ-curve theorems, small crosscuts and the
small Jordan subdomains they bound, arcs in open connected sets and in the complement of an
arc, the non-planarity of `K₃,₃`, and the completion of an arc to a closed Jordan curve.  `docs/library.md` lists these file by file.

## 2. The one open statement: Euler's inequality

`AbstractVoronoi/Jordan/PlaneGraph.lean` isolates the classical topology behind Euler's
formula in two propositions.

* `AVD.PlaneGraphVertexDegree` — a vertex of a plane graph lying on the closures of at least
  three faces is an end of at least three edges.  For arbitrary plane graphs this is not
  proved here, and it is not used: the instance the proof of Theorem 10 needs, for the
  Voronoi diagram, **is** proved (`AVD.CurveSystem.three_le_edges_at_vertex`, in
  `AbstractVoronoi/AVD/VertexDegree.lean`).
* `AVD.EulerSphereInequality` — the Euler inequality `e + 1 ⩽ v + f`.  This is the single
  unproved statement of the project, and `AVD.CurveSystem.theorem10` takes it as the
  explicit hypothesis `hEuler`.

Everything else the count needs is proved: the diagram is a finite plane graph whose faces
are its non-empty Voronoi regions (at most `n` of them), every Voronoi vertex lies on the
closures of at least three faces, the handshake inequality `3v ⩽ 2e`
(`AVD.IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge`), and the counting that turns the
two inputs into the bounds the paper uses
(`AVD.IsFinitePlaneGraph.ncard_le_of_degree`).

The degree condition is proved as follows (`AVD/VertexDegree.lean`, `Jordan/LocalFaces.lean`,
`Jordan/ArcCompletion.lean`): near a point, the diagram consists of that point and of the
edges ending there; if those all lie on a single bisecting curve then at most two faces meet
there; and if exactly two edges end at the vertex, each of them is near the vertex a single
branch of its curve, so the two together form an arc through the vertex, which lies on a
closed Jordan curve — again at most two faces.  Since three faces meet at a Voronoi vertex,
at least three edges end there.

Proving `AVD.EulerSphereInequality` is the natural next piece of work.  The usual route is
induction on the number of edges: removing an edge that lies on two distinct faces merges
them, and removing a pendant edge leaves the faces unchanged — each step needs the Jordan
curve theorem to know how the faces behave, which is exactly the part no available library
provides.  That is a substantial development in its own right, comparable in size to the
planar topology already in `AbstractVoronoi/Jordan/`.  Section 4 of
`euler-formula-and-counting.md` explains why the existing Lean formalizations of Euler's
formula do not supply it.

## 3. Smaller things that could still be improved

* The Euler-free edge bound `AVD.CurveSystem.edgeSet_ncard_le` sums over the `C(n,2)`
  unordered pairs of sites, giving `C(n,2)·(2·C(n,3) + 1)`.  It is in any case far from the
  truth.
* Once `AVD.EulerSphereInequality` is proved, the conclusion of `AVD.EulerPlaneBounds` can be
  sharpened from `v ⩽ 2f`, `e ⩽ 3f` to the classical `v ⩽ 2f - 4`, `e ⩽ 3f - 6` for graphs
  with at least one edge, and `AVD.CurveSystem.theorem10` would then give `2n - 4` and
  `3n - 6`.
* Lemma 7 (ii) is stated in the orientation-free form (the two branches lie in the closures
  of *different* half-planes) because the paper's orientation convention ("`D(p,r)` lies on
  the right-hand side of `J(p,r)` as `t → +∞`") is not formalized.  Formalizing plane
  orientation along a properly embedded line would let the statement follow the paper
  literally; it is not needed anywhere in the development.
* The clause "the boundary of `U` is a closed Jordan curve" of Theorem 4 is used nowhere
  after Theorem 4; this is recorded by the split between `AVD.JordanCurveAccessibility` and
  `AVD.JordanCurveLocalStructure`.
* The formalization stops at Theorem 10.  Sections 4 and following of the paper (Lemma 11
  onwards, the randomized incremental construction) are untouched and would be the natural
  mathematical continuation.
