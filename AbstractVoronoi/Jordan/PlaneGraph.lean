import AbstractVoronoi.Jordan.Sphere
import AbstractVoronoi.Jordan.LineComponents

/-!
# Finite plane graphs, their faces, and Euler's formula

This file develops the plane graph theory used in the proof of
**Theorem 10** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

takes for granted:

> The abstract Voronoi diagram `V(S)`, where `|S| = n`, is a planar graph of `O(n)` edges and
> vertices.

The paper obtains the count `O(n)` from **Euler's formula** `v - e + f = 2` for connected
plane graphs, together with the two standard side conditions: the faces of `V(S)` are the
Voronoi regions, of which there are at most `n`, and every Voronoi vertex is incident with at
least three edges.

The notions used to state this are:

* `AVD.faceSet G` — the *faces* of a plane set `G`, i.e. the connected components of its
  complement;
* `AVD.IsFinitePlaneGraph Vtx Edg` — what it means for a finite set `Vtx` of points and a
  finite set `Edg` of pairwise disjoint open arcs to form a *finite plane graph*;
* `AVD.EulerFormula` and `AVD.EulerPlaneBounds` — Euler's formula for a bounded connected
  plane graph, and the linear bounds on the numbers of vertices and edges that it yields for
  a plane graph all of whose vertices lie on the closures of at least three faces.

Two steps of the classical argument are proved here:

* an edge of a finite plane graph has at most two ends
  (`AVD.IsFinitePlaneGraph.edge_ends_ncard_le_two`), since it is an open subarc of a properly
  embedded line and an open interval has at most two finite ends;
* the **handshake inequality** `3v ⩽ 2e` for a plane graph whose vertices are ends of at
  least three edges (`AVD.IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge`), and with it the
  derivation of the bounds `AVD.EulerPlaneBounds` from the Euler inequality
  (`AVD.eulerPlaneBounds_of_eulerSphereInput`).

What remains unproved are the two classical facts, here kept apart as two propositions:

* `AVD.PlaneGraphVertexDegree` — a vertex lying on the closures of three faces is an end of at
  least three edges.  This is stated here for arbitrary plane graphs, where it is not proved,
  but it is not used: for the Voronoi diagram, which is the only case the proof of Theorem 10
  needs, it is *proved* (`AVD.CurveSystem.three_le_edges_at_vertex`);
* `AVD.EulerSphereInequality` — the Euler inequality `e + 1 ⩽ v + f` for plane graphs.

The second of these is the one statement that the proof of `AVD.CurveSystem.theorem10` still
takes on faith (it appears there as a single `sorry`).  Everything else the theorem asserts —
including the explicit bound `2·C(n,3)` on the number of vertices coming from Lemma 9 — is
proved.
-/

noncomputable section

open Set Topology

namespace AVD

/-- The **faces** of a plane set `G`: the connected components of the complement of `G`.

For the Voronoi diagram `V(S)` of an admissible curve system these are exactly the non-empty
Voronoi regions (`AVD.CurveSystem.faceSet_V_eq`). -/
def faceSet (G : Set Plane) : Set (Set Plane) :=
  {F | ∃ z ∈ Gᶜ, F = connectedComponentIn Gᶜ z}

/-- `Vtx` and `Edg` form a **finite plane graph**: `Vtx` is a finite set of points of the
plane (the *vertices*), `Edg` is a finite set of pairwise disjoint connected sets (the
*edges*), disjoint from `Vtx`, each of which is an open subarc of a properly embedded line of
the plane, and the ends of an edge — the points of its closure that are not on it — are
vertices.  The union `Vtx ∪ ⋃ Edg` of the graph is required to be closed.

This is the shape of the plane graph produced by Theorem 10 of
Klein–Langetepe–Nilforoushan (2009): the vertices are the points lying on at least three
Voronoi region boundaries, and the edges are the connected components of the rest of the
diagram, each of which is an open piece of a bisecting curve.  Unbounded edges are allowed,
since bisecting curves are unbounded. -/
structure IsFinitePlaneGraph (Vtx : Set Plane) (Edg : Set (Set Plane)) : Prop where
  /-- There are finitely many vertices. -/
  vtx_finite : Vtx.Finite
  /-- There are finitely many edges. -/
  edge_finite : Edg.Finite
  /-- Every edge is connected and non-empty. -/
  edge_isConnected : ∀ e ∈ Edg, IsConnected e
  /-- Distinct edges are disjoint. -/
  edge_disjoint : ∀ e ∈ Edg, ∀ e' ∈ Edg, e ≠ e' → Disjoint e e'
  /-- No edge passes through a vertex. -/
  vtx_disjoint : Disjoint Vtx (⋃₀ Edg)
  /-- Every edge is an open subarc of a properly embedded line of the plane. -/
  edge_isArc : ∀ e ∈ Edg, ∃ (γ : ℝ → Plane) (L : Set Plane) (I : Set ℝ),
    IsProperLineParam γ L ∧ IsOpen I ∧ IsPreconnected I ∧ e = γ '' I
  /-- The ends of an edge are vertices. -/
  edge_ends : ∀ e ∈ Edg, closure e \ e ⊆ Vtx
  /-- The graph is a closed subset of the plane. -/
  isClosed : IsClosed (Vtx ∪ ⋃₀ Edg)

/-- **The ends of an edge come from the ends of the parametrizing interval.**

An edge `e` of a finite plane graph is an open subarc `γ '' I` of a properly embedded line,
where `I ⊆ ℝ` is open and connected; since `γ` is a proper injective map it is a closed
embedding, so the set `closure e \ e` of ends of `e` is the image under `γ` of
`closure I \ I = frontier I`. -/
theorem IsFinitePlaneGraph.edge_ends_eq_image_frontier {Vtx : Set Plane}
    {Edg : Set (Set Plane)} (hG : IsFinitePlaneGraph Vtx Edg) {e : Set Plane} (he : e ∈ Edg) :
    ∃ (γ : ℝ → Plane) (I : Set ℝ), Function.Injective γ ∧ IsOpen I ∧ I.OrdConnected ∧
      closure e \ e = γ '' frontier I := by
  obtain ⟨γ, L, I, hγ, hIopen, hIconn, rfl⟩ := hG.edge_isArc e he
  obtain ⟨hcont, hinj, -, hproper⟩ := id hγ
  have hproperMap : IsProperMap γ := isProperMap_iff_isCompact_preimage.2 ⟨hcont, hproper⟩
  refine ⟨γ, I, hinj, hIopen, hIconn.ordConnected, ?_⟩
  have hclosure : closure (γ '' I) = γ '' closure I := by
    refine Subset.antisymm (closure_minimal (image_mono subset_closure)
      (hproperMap.isClosedMap _ isClosed_closure)) ?_
    exact image_closure_subset_closure_image hcont
  have hfront : closure I \ I = frontier I := by
    rw [frontier, hIopen.interior_eq]
  rw [hclosure, ← Set.image_sdiff hinj, hfront]

/-- The set of ends of an edge of a finite plane graph is finite. -/
theorem IsFinitePlaneGraph.edge_ends_finite {Vtx : Set Plane} {Edg : Set (Set Plane)}
    (hG : IsFinitePlaneGraph Vtx Edg) {e : Set Plane} (he : e ∈ Edg) :
    (closure e \ e).Finite := by
  obtain ⟨γ, I, -, hIopen, hord, hEq⟩ := hG.edge_ends_eq_image_frontier he
  rw [hEq]
  exact (frontier_finite_of_ordConnected hIopen hord).image γ

/-- **An edge of a finite plane graph has at most two ends.**

The parametrizing interval `I` has at most the two finite ends `sInf I` and `sSup I`, and the
ends of the edge are their images.

This is the geometric input of the handshake count used in the proof of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009): each edge contributes at most two incidences with the
vertex set. -/
theorem IsFinitePlaneGraph.edge_ends_ncard_le_two {Vtx : Set Plane} {Edg : Set (Set Plane)}
    (hG : IsFinitePlaneGraph Vtx Edg) {e : Set Plane} (he : e ∈ Edg) :
    (closure e \ e).ncard ≤ 2 := by
  obtain ⟨γ, I, hinj, hIopen, hord, hEq⟩ := hG.edge_ends_eq_image_frontier he
  rw [hEq, Set.ncard_image_of_injective _ hinj]
  exact frontier_ncard_le_two_of_ordConnected hIopen hord

/-- **The handshake inequality for a finite plane graph.**

If every vertex of a finite plane graph is an end of at least three edges, then
`3·v ⩽ 2·e`: counting the incidences `(vertex, edge)` in two ways, each vertex contributes at
least three of them, while each edge contributes at most two, because an edge has at most two
ends (`AVD.IsFinitePlaneGraph.edge_ends_ncard_le_two`).

This is the first half of the classical chain of inequalities by which the proof of
**Theorem 10** of Klein–Langetepe–Nilforoushan (2009) derives the count `O(n)` of vertices
and edges from Euler's formula. -/
theorem IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge {Vtx : Set Plane}
    {Edg : Set (Set Plane)} (hG : IsFinitePlaneGraph Vtx Edg)
    (hdeg : ∀ v ∈ Vtx, 3 ≤ {e ∈ Edg | v ∈ closure e}.ncard) :
    3 * Vtx.ncard ≤ 2 * Edg.ncard := by
  classical
  set VF : Finset Plane := hG.vtx_finite.toFinset with hVF
  set EF : Finset (Set Plane) := hG.edge_finite.toFinset with hEF
  have hVcard : Vtx.ncard = VF.card := by
    rw [hVF, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  have hEcard : Edg.ncard = EF.card := by
    rw [hEF, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  -- each vertex is an end of at least three edges
  have hlow : ∀ v ∈ VF, 3 ≤ ∑ e ∈ EF, (if v ∈ closure e then 1 else 0) := by
    intro v hv
    have hvVtx : v ∈ Vtx := by rwa [hVF, Set.Finite.mem_toFinset] at hv
    have hcoe : ((EF.filter fun e => v ∈ closure e : Finset (Set Plane)) : Set (Set Plane))
        = {e ∈ Edg | v ∈ closure e} := by
      ext e
      simp [hEF, Set.Finite.mem_toFinset, and_comm]
    have := hdeg v hvVtx
    rw [← hcoe, Set.ncard_coe_finset] at this
    rw [← Finset.card_filter]
    exact this
  -- each edge has at most two ends
  have hhigh : ∀ e ∈ EF, ∑ v ∈ VF, (if v ∈ closure e then 1 else 0) ≤ 2 := by
    intro e he
    have heEdg : e ∈ Edg := by rwa [hEF, Set.Finite.mem_toFinset] at he
    have hsub : ((VF.filter fun v => v ∈ closure e : Finset Plane) : Set Plane)
        ⊆ closure e \ e := by
      intro v hv
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hVF, Set.Finite.mem_toFinset] at hv
      refine ⟨hv.2, ?_⟩
      intro hve
      exact (Set.disjoint_left.1 hG.vtx_disjoint hv.1) ⟨e, heEdg, hve⟩
    have hle : (VF.filter fun v => v ∈ closure e).card ≤ (closure e \ e).ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (hG.edge_ends_finite heEdg)
    rw [← Finset.card_filter]
    exact hle.trans (hG.edge_ends_ncard_le_two heEdg)
  calc 3 * Vtx.ncard = ∑ _v ∈ VF, 3 := by
        rw [hVcard, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ v ∈ VF, ∑ e ∈ EF, (if v ∈ closure e then 1 else 0) := Finset.sum_le_sum hlow
    _ = ∑ e ∈ EF, ∑ v ∈ VF, (if v ∈ closure e then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _e ∈ EF, 2 := Finset.sum_le_sum hhigh
    _ = 2 * Edg.ncard := by
        rw [hEcard, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Euler's formula** for a bounded connected finite plane graph: if the graph
`Vtx ∪ ⋃ Edg` is connected and bounded (so that all of its edges are bounded arcs) and has
finitely many faces, then

`(number of vertices) + (number of faces) = (number of edges) + 2`,

the faces being the connected components of the complement of the graph, the unbounded one
included.

This proposition is *not* proved in this development.  It is stated for reference: it is the
classical form of the statement that the proof of Theorem 10 of
Klein–Langetepe–Nilforoushan (2009) appeals to.  What that proof actually uses is the
consequence `AVD.EulerPlaneBounds` below, which also covers the unbounded edges occurring in
a Voronoi diagram. -/
def EulerFormula : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    IsConnected (Vtx ∪ ⋃₀ Edg) → Bornology.IsBounded (Vtx ∪ ⋃₀ Edg) →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    Vtx.ncard + (faceSet (Vtx ∪ ⋃₀ Edg)).ncard = Edg.ncard + 2

/-- The **counting consequence of Euler's formula** used in the proof of Theorem 10 of
Klein–Langetepe–Nilforoushan (2009): for a finite plane graph with finitely many faces, in
which every vertex lies on the closures of at least three faces, the number of vertices is at
most twice, and the number of edges at most three times, the number of faces.

This is the classical chain: a point lying on the closures of three faces is incident with at
least three edges, so `2·e ⩾ 3·v` by the handshake lemma, while Euler's formula on the sphere
— the plane graph compactified by one point at infinity, which absorbs the ends of the
unbounded edges — gives `v - e + f ⩾ 2 - 1`; eliminating `v` yields `e ⩽ 3f - 3` and
`v ⩽ 2f - 2`.  The bounds are stated with this slack, in the form in which the paper uses
them: with at most `n` faces one gets `O(n)` vertices and edges.

Only the two classical inputs to this chain are taken on faith here, in the form of
`AVD.EulerSphereInput`; the counting itself is proved, in
`AVD.eulerPlaneBounds_of_eulerSphereInput`.  For the Voronoi diagram the first of the two,
the degree condition, is proved (`AVD.CurveSystem.three_le_edges_at_vertex`), so that only
the Euler inequality is left. -/
def EulerPlaneBounds : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    (∀ v ∈ Vtx, 3 ≤ {F ∈ faceSet (Vtx ∪ ⋃₀ Edg) | v ∈ closure F}.ncard) →
    Vtx.ncard ≤ 2 * (faceSet (Vtx ∪ ⋃₀ Edg)).ncard ∧
      Edg.ncard ≤ 3 * (faceSet (Vtx ∪ ⋃₀ Edg)).ncard

/-- The **degree condition** of the Euler count, as a statement about plane graphs: in a
finite plane graph with finitely many faces, a vertex lying on the closures of at least three
faces is an end of at least three edges — three faces meeting at a point must be separated
near it by three different edges.

This proposition is **not proved** in this development for arbitrary plane graphs, and it is
no longer used: the instance of it that the proof of Theorem 10 needs, the one for the
Voronoi diagram of an admissible curve system, is proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).  It is kept here because it is the classical
statement the paper appeals to. -/
def PlaneGraphVertexDegree : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    (∀ v ∈ Vtx, 3 ≤ {F ∈ faceSet (Vtx ∪ ⋃₀ Edg) | v ∈ closure F}.ncard) →
    ∀ v ∈ Vtx, 3 ≤ {e ∈ Edg | v ∈ closure e}.ncard

/-- The **Euler inequality on the sphere**, `e + 1 ⩽ v + f`, for a finite plane graph with
finitely many faces: compactifying the plane by one point at infinity, which absorbs the ends
of the unbounded edges, turns the graph into a graph on the sphere with at most one extra
vertex, for which `v - e + f ⩾ 2`.

This proposition is **not proved** in this development; it is Euler's formula for embedded
plane graphs, which no available library supplies (see `notes/euler-formula-and-counting.md`).
It is the one statement that the proof of `AVD.CurveSystem.theorem10` still takes on faith. -/
def EulerSphereInequality : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    Edg.ncard + 1 ≤ Vtx.ncard + (faceSet (Vtx ∪ ⋃₀ Edg)).ncard

/-- The **two classical facts of plane topology** on which the Euler count of the proof of
Theorem 10 of Klein–Langetepe–Nilforoushan (2009) rests: the degree condition
`AVD.PlaneGraphVertexDegree` and the Euler inequality `AVD.EulerSphereInequality`.

Neither of the two is proved here; the counting that turns them into the bounds the paper
uses is (`AVD.eulerPlaneBounds_of_eulerSphereInput`). -/
def EulerSphereInput : Prop := PlaneGraphVertexDegree ∧ EulerSphereInequality

/-- **The counting step of the Euler bounds is proved here**, in the form in which the proof
of Theorem 10 uses it: for a finite plane graph with finitely many faces *each of whose
vertices is an end of at least three edges*, the Euler inequality `e + 1 ⩽ v + f` gives
`v ⩽ 2f` and `e ⩽ 3f`.

The handshake inequality `3v ⩽ 2e` (`AVD.IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge`)
combined with `e ⩽ v + f - 1` gives `v ⩽ 2f - 2` and then `e ⩽ 3f - 3`. -/
theorem IsFinitePlaneGraph.ncard_le_of_degree {Vtx : Set Plane} {Edg : Set (Set Plane)}
    (hG : IsFinitePlaneGraph Vtx Edg) (hfaces : (faceSet (Vtx ∪ ⋃₀ Edg)).Finite)
    (hdeg : ∀ v ∈ Vtx, 3 ≤ {e ∈ Edg | v ∈ closure e}.ncard) (heuler : EulerSphereInequality) :
    Vtx.ncard ≤ 2 * (faceSet (Vtx ∪ ⋃₀ Edg)).ncard ∧
      Edg.ncard ≤ 3 * (faceSet (Vtx ∪ ⋃₀ Edg)).ncard := by
  have hhand : 3 * Vtx.ncard ≤ 2 * Edg.ncard := hG.three_mul_vtx_le_two_mul_edge hdeg
  have hEuler := heuler Vtx Edg hG hfaces
  omega

/-- **The counting step of the Euler bounds is proved here.**

From the two classical inputs of `AVD.EulerSphereInput` — every vertex is an end of at least
three edges, and the Euler inequality `e + 1 ⩽ v + f` on the sphere — the bounds
`v ⩽ 2f` and `e ⩽ 3f` of `AVD.EulerPlaneBounds` follow by pure counting
(`AVD.IsFinitePlaneGraph.ncard_le_of_degree`).

This is the chain of inequalities by which the proof of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009) obtains its count `O(n)` of vertices and edges. -/
theorem eulerPlaneBounds_of_eulerSphereInput (h : EulerSphereInput) : EulerPlaneBounds := by
  intro Vtx Edg hG hfaces hdeg
  exact hG.ncard_le_of_degree hfaces (h.1 Vtx Edg hG hfaces hdeg) h.2

end AVD
