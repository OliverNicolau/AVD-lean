# Statement-by-statement check against the paper

A re-reading of

> R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
> Computational Geometry 42 (2009) 885–902,

Section 2 and Section 3, against the formal statements of `AbstractVoronoi/Paper/`.  For
each numbered item: what the paper says, what the Lean declaration says, and where the two
differ.  Everything listed here is proved, with no open hypothesis, except for one assertion
of Theorem 10: its `O(n)` count, which rests on Euler's inequality
`AVD.EulerSphereInequality`, stated but not proved and taken as the explicit hypothesis
`hEuler` of the theorem (the project contains no `sorry`).  The
other input of that count, the degree condition at a Voronoi vertex, *is* proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).

| paper | Lean declaration | verdict |
| --- | --- | --- |
| data of Section 2 (`J(p,q) = J(q,p)`, the two domains `D(p,q)`, `D(q,p)`) | `AVD.CurveSystem` | faithful, and slightly more general; the symmetry `J(p,q) = J(q,p)` is *derived* (`AVD.CurveSystem.J_symm`) instead of assumed, and so are the non-emptiness, the connectedness and the unboundedness of the two domains (see the remark below) |
| equations (1), (2) | `AVD.CurveSystem.VR`, `AVD.CurveSystem.V` | literal |
| Definition 1 (`A₁`, `A₂`, `A₃`) | `AVD.CurveSystem.Admissible` | literal (see the two remarks below) |
| Definition 2 | `AVD.CurveSystem.voronoiRegion`, `AVD.CurveSystem.voronoiDiagram` | literal |
| Lemma 3 | `AVD.CurveSystem.lemma3` | literal (both equalities) |
| Theorem 4 | `AVD.JordanCurveAccessibility`, `AVD.theorem4` | faithful, with `U` allowed arbitrarily small |
| Lemma 5 | `AVD.CurveSystem.lemma5` | literal |
| Lemma 6 | `AVD.CurveSystem.lemma6` | literal, with "consecutively visited" read off a proper parametrization |
| Lemma 7 (i) | `AVD.CurveSystem.lemma7_touching` | literal |
| Lemma 7 (ii) | `AVD.CurveSystem.lemma7_crossing` | faithful, stated without the paper's orientation convention |
| Lemma 8 | `AVD.CurveSystem.lemma8` | literal |
| Lemma 9 | `AVD.CurveSystem.lemma9` | faithful; the hypothesis `n ⩾ 3` is not needed |
| Theorem 10 | `AVD.CurveSystem.theorem10` | literal, plus the hypothesis `hEuler`; the plane-graph structure and the degree condition at a Voronoi vertex are proved, and the `O(n)` count rests on the stated but unproved `AVD.EulerSphereInequality`, taken as the hypothesis `hEuler` |

## Remarks on the individual items

**Definition 1.**  Axiom `A₁` is stated as in the paper: a bisecting curve is mapped to a
closed Jordan curve *through the north pole* by stereographic projection to the sphere
(`AVD.IsUnboundedJordanCurve`, and footnote 4 of the paper for the completion by the north
pole).  Axiom `A₂` is stated as "any two points of `VR(p', S')` can be joined by a path
inside it", which allows empty regions — as it must, since the proof of Lemma 9 in the paper
considers the case of an empty Voronoi region.  Axiom `A₃` is the stated equality
`ℝ² = ⋃_{p' ∈ S'} closure (VR(p', S'))`.

**The data of Section 2.**  The paper asks that each curve `J(p,q)` split the plane into two
*unbounded domains* `D(p,q)`, `D(q,p)`.  The structure `AVD.CurveSystem` is slightly more
general: it only requires the two labelled pieces to be open, disjoint, preconnected and
complementary to the curve.  This loses nothing, because for an *admissible* system the
missing properties are theorems: axiom `A₁` forces each piece to be non-empty
(`AVD.CurveSystem.D_nonempty`), hence a domain (`AVD.CurveSystem.D_isConnected`), and
unbounded (`AVD.CurveSystem.D_not_isBounded`, from the fact that the common boundary of the
two pieces is the unbounded curve `J(p,q)` itself, `AVD.IsUnboundedJordanCurve.not_isBounded`).
Accordingly, the lemmas that identify the two pieces with the two complementary domains of
the Jordan curve theorem — `AVD.CurveSystem.D_eq_of_separation`,
`AVD.CurveSystem.D_pair_eq_of_separation` and everything downstream — carry the
admissibility hypothesis.

**Theorem 4.**  The global part ("`ℝ² \ C` consists of two domains `D₁, D₂` with common
boundary `C`") and the local part (a neighbourhood `U` bounded by a closed Jordan curve,
with `U \ C` having exactly two components, from each of which `z` is accessible) are both
formalized, for closed Jordan curves and for the unbounded curves of axiom `A₁`.  Two
readings had to be fixed: "`U \ C` consists of exactly two connected components" is rendered
as "`U ∩ D₁` and `U ∩ D₂` are connected and non-empty" (they are disjoint and cover `U \ C`),
and "there exists a neighbourhood `U`" is strengthened to "arbitrarily small such `U` exist",
which is how the paper later uses the theorem.

**Lemma 6.**  "Four points consecutively visited by `J(p,r)`" is `g t₁, g t₂, g t₃, g t₄`
with `t₁ < t₂ < t₃ < t₄`, for a proper parametrization `g` of `J(p,r)`; that such a
parametrization exists is proved from axiom `A₁`
(`AVD.IsUnboundedJordanCurve.exists_properParam`).  "Alternately" covers both patterns.

**Lemma 7.**  `F∓`, `G∓` are the four branches of the discussion preceding the lemma,
formalized as `AVD.BranchBefore`/`AVD.BranchAfter` ("`g((-δ,0)) ⊆ A` for some `δ > 0`").
Part (i) is stated exactly as in the paper, with the closures of the half-planes.  Part (ii)
is stated with the same closures, and its conclusion is the orientation-free statement that
the two branches of `J(p,r)` lie in the closures of *different* half-planes of `J(p,q)` —
the paper's claim together with its "`+` and `−` reversed" variant, since the formalization
does not fix the orientation convention "`D(p,r)` lies on the right hand side of `J(p,r)` as
`t` tends to `+∞`".  Of the four non-degeneracy conditions of footnote 8, only the two
concerning the branches of `J(p,q)` are used.

**Lemma 8.**  "A point `w` on the boundary of `VR(p, S)`, where `|S| = 3`" is
`w ∈ frontier (C.VR p S')` for a subset `S' ⊆ S` with `S'.card = 3`, and the conclusion is
`AccessibleFrom (C.VR p S') w`: an arc `α` with endpoint `w` and `α \ {w} ⊆ VR(p, S')`.

**Lemma 9.**  `B` is the set of points lying on the boundaries of at least three Voronoi
regions of *some* diagram `V(S')` with `S' ⊆ S` (`AVD.CurveSystem.BSet`), and the conclusion
is that `B` is finite of cardinality at most `2·C(n,3)`.

**Theorem 10.**  "Finite plane graph" is formalized as: `V(S)` is the disjoint union of its
set of Voronoi vertices and of its edges; the edges are the connected components of `V(S)`
minus the vertices; distinct edges are disjoint; each edge is connected and contained in a
single bisecting curve `J(p,q)`; and there are finitely many vertices and edges.  All of
that is proved.  The `O(n)` count of the paper is the only numerical assertion of the formal
statement (`|B'| ⩽ 2n` and `|E| ⩽ 3n`), so that the statement stays close to the printed one,
and it is the one assertion of the development that is not proved: it is
deduced, by a proved counting argument (`AVD.IsFinitePlaneGraph.ncard_le_of_degree`), from the
proved degree condition at a Voronoi vertex (at least three edges end at it,
`AVD.CurveSystem.three_le_edges_at_vertex`) and from `AVD.EulerSphereInequality`, the
explicit hypothesis `hEuler` of the theorem.  What that deduction needs about the diagram *is*
proved: the diagram is a finite plane graph (`AVD.CurveSystem.isFinitePlaneGraph`), its faces
are the non-empty Voronoi regions, of which there are at most `n`
(`AVD.CurveSystem.faceSet_V_eq`, `…faceSet_V_ncard_le`), and each Voronoi vertex lies on the
closures of at least three faces (`AVD.CurveSystem.three_le_faces_at_vertex`).  The vertex
`∞` of the paper (the north pole) does not appear: the formal plane graph lives in `ℝ²`, and
the compactification is accounted for by the slack in the bounds `AVD.EulerPlaneBounds`
(`2f` and `3f` instead of `2f - 4` and `3f - 6`).  Sharper bounds that avoid Euler's formula
are proved as separate lemmas, and are not part of the statement of Theorem 10: at most
`2·C(n,3)` vertices (`AVD.CurveSystem.vertexSet_ncard_le`) and at most
`C(n,2)·(2·C(n,3) + 1)` edges (`AVD.CurveSystem.edgeSet_ncard_le`).  See
`notes/euler-formula-and-counting.md`.
