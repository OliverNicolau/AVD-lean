# Euler's formula and the `O(n)` count of Theorem 10

Theorem 10 of Klein–Langetepe–Nilforoushan (2009) states that the Voronoi diagram `V(S)` of
an admissible system of `n` bisecting curves is a plane graph of `O(n)` edges and vertices.
The plane-graph structure is proved here in full; the count `O(n)` is obtained in the paper
from **Euler's formula for plane graphs**, which is the one statement this development does
not prove.  This note records how that is handled, and why an existing Lean formalization of
Euler's formula does not help.

## 1. What is stated, and where the `sorry` is

`AbstractVoronoi/Jordan/PlaneGraph.lean` introduces

* `AVD.faceSet G` — the **faces** of a plane set `G`: the connected components of `Gᶜ`;
* `AVD.IsFinitePlaneGraph Vtx Edg` — a finite set `Vtx` of vertices and a finite set `Edg` of
  pairwise disjoint edges, each an open subarc of a properly embedded line of the plane, no
  edge meeting a vertex, the ends of an edge (the points of `closure e \ e`) being vertices,
  and `Vtx ∪ ⋃ Edg` closed;
* `AVD.EulerFormula` — Euler's formula `v + f = e + 2` for a **bounded connected** finite
  plane graph, stated for reference;
* `AVD.EulerPlaneBounds` — the counting consequence that the paper uses: for a finite plane
  graph with finitely many faces in which every vertex lies on the closures of at least three
  faces, `v ⩽ 2f` and `e ⩽ 3f`;
* `AVD.PlaneGraphVertexDegree` and `AVD.EulerSphereInequality` — the two classical facts of
  plane topology from which those bounds follow, kept apart as two propositions: every vertex
  of such a graph is an end of at least three edges, and the Euler inequality
  `e + 1 ⩽ v + f`.  Their conjunction is `AVD.EulerSphereInput`.

The degree condition is no longer assumed at all: its instance for the Voronoi diagram, which
is what the proof of Theorem 10 needs, is **proved**
(`AVD.CurveSystem.three_le_edges_at_vertex`) — see section 5 below.  What remains assumed is
the Euler inequality alone.

Two steps of the classical argument are proved here rather than assumed:

* an **edge has at most two ends** (`AVD.IsFinitePlaneGraph.edge_ends_ncard_le_two`): an edge
  is `γ '' I` for a proper injective parametrization `γ` of a line and an open interval `I`,
  so its set of ends is `γ '' frontier I`, and `frontier I ⊆ {sInf I, sSup I}`;
* the **handshake inequality** `3v ⩽ 2e`
  (`AVD.IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge`), by counting the incidences
  `(vertex, edge)` of the graph in two ways.

With them, `AVD.EulerPlaneBounds` is *derived* from `AVD.EulerSphereInput`
(`AVD.eulerPlaneBounds_of_eulerSphereInput`, through
`AVD.IsFinitePlaneGraph.ncard_le_of_degree`): `3v ⩽ 2e` and `e + 1 ⩽ v + f` give `v ⩽ 2f - 2`
and `e ⩽ 3f - 3`.

`AVD.EulerSphereInequality` is therefore the only statement invoked by the proof of
`AVD.CurveSystem.theorem10` through a `sorry`, and `AVD.CurveSystem.theorem10` is the only
declaration of the project that depends on `sorryAx` (checked with `#print axioms`).

The bounds are stated with slack (`2f` and `3f` rather than `2f - 4` and `3f - 6`) because
the graph may be disconnected and its edges may be unbounded, as they are for a Voronoi
diagram: on the sphere, compactifying by one point at infinity that absorbs the ends of the
unbounded edges, Euler's formula reads `v' - e + f = 1 + c ⩾ 2` with `v' ⩽ v + 1`, while the
degree condition gives `2e ⩾ 3v`; eliminating `v` yields `e ⩽ 3f - 3` and `v ⩽ 2f - 2`.

## 2. What the proof of Theorem 10 supplies, and what it assumes

Everything the Euler count is applied to is proved:

* the diagram is a finite plane graph in the above sense
  (`AVD.CurveSystem.isFinitePlaneGraph`).  The one new ingredient is the structure of an
  edge: an edge is a connected component of `V(S)` minus the Voronoi vertices, it lies in one
  set `B_{p,q}`, and on a proper parametrization `g` of `J(p,q)` it is the image of a
  connected component of an open subset of the line, whose ends are frontier points of that
  set, hence Voronoi vertices (`AVD.CurveSystem.edge_isSubarc_and_ends`, resting on
  `AVD.closure_connectedComponentIn_diff_subset_frontier` and
  `AVD.CurveSystem.frontier_preimage_UPair_subset`);
* the **faces are the Voronoi regions** (`AVD.CurveSystem.faceSet_V_eq`): the complement of
  the diagram is the union of the regions, which are open, pairwise disjoint and
  path-connected by axiom `A₂`, so the non-empty ones are exactly the connected components of
  the complement.  Hence there are at most `n` faces
  (`AVD.CurveSystem.faceSet_V_ncard_le`);
* every **Voronoi vertex lies on the closures of at least three faces**
  (`AVD.CurveSystem.three_le_faces_at_vertex`): by definition it lies on the boundaries of
  three distinct regions, and distinct non-empty regions are distinct faces.

Only one thing is assumed: the Euler inequality `e + 1 ⩽ v + f` itself.  That a Voronoi vertex
is an end of at least three edges is proved (section 5), and so is the counting that turns
the two into the numerical bounds.

## 3. Importing an existing Lean proof of Euler's formula

The repository <https://github.com/JMR-Independent/lean-euler-formula> was examined as a
possible dependency.  Two independent obstacles were found.

**(a) It proves Euler's formula for a combinatorial object, not for an embedded plane
graph.**  Its central notion is an inductive predicate on triples of natural numbers,

```
inductive PlanarGraph : ℕ → ℕ → ℕ → Prop where
  | point : PlanarGraph 1 0 1
  | addLeaf (v e f : ℕ) : PlanarGraph v e f → PlanarGraph (v + 1) (e + 1) f
  | addEdge (v e f : ℕ) : PlanarGraph v e f → PlanarGraph v (e + 1) (f + 1)
```

and `euler_formula : PlanarGraph v e f → v + f = e + 2` is an induction over these three
constructors.  The constructors are exactly the operations that preserve `V - E + F`, so the
formula itself is arithmetic; all the topology sits in the statement that the graph one has
in hand is generated by them.  The repository's README says so explicitly: the bridge from
"topologically embedded in `ℝ²`" to its `PlanarGraph` predicate is listed as open work, and
the Jordan-curve route to it is not pursued there.

For Theorem 10 it is precisely that bridge that is needed: what this development has is a
plane graph in the topological sense, and turning it into an inductive construction by
`point`/`addLeaf`/`addEdge` — equivalently, producing a spanning-tree decomposition of the
embedded graph and counting its faces — is the entire difficulty.  Importing the repository
would not reduce it.

**(b) Toolchain and Mathlib version.**  That project is pinned to `leanprover/lean4:v4.29.1`
with Mathlib `v4.29.1`, while this project is pinned to `leanprover/lean4:v4.32.2` with
Mathlib `v4.32.2` (forced by the Jordan–Schönflies dependency, which supplies the Jordan
curve theorem and the Jordan–Schönflies theorem used throughout).  A single Lake build can
contain only one revision of Mathlib, so importing it would require porting one side of the
pair.  Given (a), that work would buy nothing for Theorem 10.

**Conclusion.**  The import was considered and rejected.  Nothing in that repository shortens
the path from the topological plane graph of Theorem 10 to the `O(n)` count; proving
`AVD.EulerSphereInput` here would mean formalizing Euler's formula for embedded plane graphs
from scratch, a project of its own.

## 4. What can be had without Euler's formula

Two unconditional bounds are proved.  They are kept as separate lemmas, so that the
statement of Theorem 10 mentions only the `O(n)` count of the paper:

* the number of **Voronoi vertices** is at most `2·C(n,3)` (Lemma 9,
  `AVD.CurveSystem.vertexSet_ncard_le`);
* the number of **Voronoi edges** is at most `C(n,2)·(2·C(n,3) + 1)`
  (`AVD.CurveSystem.edgeSet_ncard_le`): an open subset of the line has at most one more
  connected component than it has frontier points (`AVD.ncard_components_le_frontier`), which
  bounds by `2·C(n,3) + 1` the number of edges lying on one bisecting curve
  (`AVD.CurveSystem.ncard_edges_in_BPair_le`), and there are `C(n,2)` unordered pairs of
  sites.

These are polynomial, not linear, and so do not recover the paper's `O(n)`; that really does
need Euler's formula.

## 5. The degree condition at a Voronoi vertex: how it is proved

The degree condition — *at least three edges end at a Voronoi vertex* — is the half of the
Euler input that is about the diagram rather than about counting, and it is now **proved**
(`AVD.CurveSystem.three_le_edges_at_vertex`).  The relevant file is
`AbstractVoronoi/AVD/VertexDegree.lean`, built on the general lemmas of
`AbstractVoronoi/Jordan/LocalFaces.lean` and `AbstractVoronoi/Jordan/ArcCompletion.lean`.

### 5.1 The local picture at a point of the diagram

`AVD.CurveSystem.exists_nbhd_V_inter_subset`: for a point `z` and any neighbourhood `W` of
`z` there is an open `U ⊆ W` containing `z` with

```
V(S) ∩ U ⊆ {z} ∪ ⋃ {e edge with z ∈ closure e}.
```

Indeed the diagram is the union of its finitely many vertices and its finitely many edges
(`AVD.CurveSystem.V_eq_vertexSet_union_edges`), the other vertices are finitely many points
different from `z`, and an edge whose closure misses `z` has a closed closure missing `z`.
So near `z` only the edges *ending* at `z` are seen.

### 5.2 One curve is not enough: at most two faces

`AVD.faces_at_ncard_le_two_of_local_subset_jordan` (stated for an arbitrary closed set `G` of
the plane, since nothing about Voronoi diagrams is used): let `J` be a curve whose complement
is the union of two disjoint open domains `D₁`, `D₂` each with frontier `J` (the global part
of Theorem 4), let `U` be a neighbourhood of `z ∈ J` with `U ∩ D₁` and `U ∩ D₂` connected
(the local part of Theorem 4), and assume `G ∩ U ⊆ J`.  Then at most two faces of `G` have
`z` in their closure.

The proof is a two-case argument.

* If `J ∩ U ⊆ G`, then `U \ G = (U ∩ D₁) ∪ (U ∩ D₂)`, two connected sets, each of which lies
  inside one single face (`AVD.face_eq_of_isPreconnected`); a face whose closure contains `z`
  meets `U \ G`, hence is one of those two faces.
* If some `x ∈ J ∩ U` is off `G`, then, `G` being closed, a whole ball around `x` lies in
  `U \ G`, and it meets both `D₁` and `D₂` because `x ∈ J = frontier D₁ = frontier D₂`; so it
  joins `U ∩ D₁` to `U ∩ D₂`.  The same argument at every point of `(J ∩ U) \ G` shows that
  `U \ G` is *connected*, so only one face can meet `z`.

### 5.3 Consequence: at least two edges, on two different curves

Combining 5.1 and 5.2 with `AVD.CurveSystem.three_le_faces_at_vertex` (three faces meet at a
Voronoi vertex):

* `AVD.CurveSystem.faces_at_le_two_of_edges_subset_J` — if all the edges ending at a point of
  the diagram lie on one bisecting curve `J(p,q)` through it, at most two faces meet there;
* `AVD.CurveSystem.not_edges_at_vertex_subset_J` — hence at a Voronoi vertex the edges ending
  there never all lie on a single bisecting curve;
* `AVD.CurveSystem.exists_two_edges_at_vertex`, `AVD.CurveSystem.two_le_edges_at_vertex` —
  hence at least two distinct edges end at a Voronoi vertex, and one of them is not contained
  in the bisecting curve carrying the other.

### 5.4 The remaining case: two branches on two curves

What remained was the configuration in which exactly two edges `e₁ ⊆ J₁` and `e₂ ⊆ J₂` end at
`z`.  The picture to rule out is a disc around `z` cut into three sectors by two branches,
which is impossible because two branches issued from `z` form an *arc* through `z`.  The
argument now formalized is the following.

1. *Each edge is a single branch at `z`.*  An edge is `γ '' I` for a proper injective
   parametrization `γ` of its curve and an open interval `I`
   (`AVD.CurveSystem.edge_isSubarc_and_ends`), and `z = γ a` for an endpoint `a` of `I`.
   Properness gives, for every `δ > 0`, a ball `B` around `z` with
   `γ ⁻¹' B ⊆ (a - δ, a + δ)` (`AVD.IsProperLineParam.exists_ball_preimage_subset` in
   `AbstractVoronoi/Jordan/ProperLocal.lean`), together with the affine reparametrizations
   `AVD.IsProperLineParam.affine` that normalize `a` to `0`.  Packaged for an edge of the
   diagram, this is `AVD.CurveSystem.edge_isBranch_at_end`: near one of its ends the edge *is*
   a single branch `γ '' (0, δ)` of a proper parametrization `γ` with `γ 0 = z`, and a small
   enough ball around `z` meets the edge only inside that branch.

2. *The two branches form an arc, and the arc lies on a closed Jordan curve.*  The two
   branches are disjoint (distinct edges are disjoint) and meet only at `z`, so
   `γ₁([0,d₁]) ∪ γ₂([0,d₂])` is an arc through `z`.  Each of the two curves continues past the
   end of its branch, and those continuations stay on the corresponding edges, hence off the
   arc; so `AVD.exists_closedJordanCurve_extend` applies — the completion of the arc to a
   closed Jordan curve is obtained from the non-separation theorem for arcs (two points off an
   arc can be joined by an arc avoiding it) followed by the surgery step `AVD.exists_arc_cut`
   at both ends.  Its packaged form for two branches is
   `AVD.exists_closedJordanCurve_two_branches`.

3. *Conclusion.*  In a small enough neighbourhood of `z` the diagram is contained in that
   closed Jordan curve, so 5.2 applies verbatim: at most two faces have `z` in their closure,
   contradicting `AVD.CurveSystem.three_le_faces_at_vertex`.  Hence at least three edges end
   at every Voronoi vertex.

With this, the degree condition for the Voronoi diagram is proved outright, and Euler's
inequality is the only statement of the development left unproved.
