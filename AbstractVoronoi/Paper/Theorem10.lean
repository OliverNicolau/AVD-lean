import AbstractVoronoi.AVD.VertexDegree

/-!
# Theorem 10

**Theorem 10** of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams
revisited*, Computational Geometry 42 (2009) 885–902: the Voronoi diagram of an admissible
system of `n` bisecting curves is a plane graph of `O(n)` edges and vertices.

The plane graph structure — the diagram is the disjoint union of its finitely many Voronoi
vertices and of its finitely many edges, each edge being connected and contained in a single
bisecting curve — is proved here in full, as is the explicit bound `2·C(n,3)` on the number
of vertices coming from Lemma 9.

The count `O(n)` is the one point of this development that is not proved: the paper obtains
it from Euler's formula for plane graphs.  The theorem therefore takes a single statement as
an explicit hypothesis: the **Euler inequality** `e + 1 ⩽ v + f` (`AVD.EulerSphereInequality`).

The other half of the Euler input, the **degree condition** at a Voronoi vertex — at least
three edges end at every Voronoi vertex — is now proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).

The counting that turns the two into the bounds used by the paper is proved
(`AVD.IsFinitePlaneGraph.ncard_le_of_degree`, via the handshake inequality
`AVD.IsFinitePlaneGraph.three_mul_vtx_le_two_mul_edge`).  Everything else that
`AVD.CurveSystem.theorem10` asserts is proved, including the two facts about the diagram that
the Euler count needs: the faces of `V(S)` are the Voronoi regions, of which there are at most
`n` (`AVD.CurveSystem.faceSet_V_ncard_le`), and every Voronoi vertex lies on the closures of
at least three faces (`AVD.CurveSystem.three_le_faces_at_vertex`).
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Theorem 10** of Klein–Langetepe–Nilforoushan (2009).

> The abstract Voronoi diagram `V(S)`, where `|S| = n`, is a finite plane graph of `O(n)`
> edges and vertices.

The plane graph structure is expressed as follows.  The Voronoi diagram is the disjoint
union of its set `B'` of Voronoi vertices (the points lying on at least three region
boundaries) and of its edges, the connected components of `V(S) \ B'`; distinct edges are
disjoint, each edge is connected and contained in a single bisecting curve `J(p,q)`, and
there are only finitely many vertices and edges, at most `2n` of the former and `3n` of the
latter — the assertion "`O(n)` edges and vertices" of the paper.

The hypothesis `n ⩾ 3` used in the paper to split off the degenerate cases is not needed.

Everything in this statement is proved from Lemmas 8 and 9 except the two bounds `2n` and
`3n`, for which the proof below uses Euler's inequality `AVD.EulerSphereInequality` for
plane graphs.  That inequality is the only unproved statement of the development, and it
is the hypothesis `hEuler` of the theorem; the other ingredient of the Euler count, the
degree condition at a Voronoi vertex, is proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).

Sharper bounds that do *not* use Euler's formula, and are therefore proved outright, are
available separately: at most `2·C(n,3)` vertices by Lemma 9
(`AVD.CurveSystem.vertexSet_ncard_le`) and at most `C(n,2)·(2·C(n,3) + 1)` edges
(`AVD.CurveSystem.edgeSet_ncard_le`). -/
theorem theorem10 (hEuler : EulerSphereInequality) (hadm : C.Admissible) :
    C.V S = C.vertexSet S ∪ ⋃₀ C.edgeSet ∧
      Disjoint (C.vertexSet S) (⋃₀ C.edgeSet) ∧
      (∀ e ∈ C.edgeSet, IsConnected e ∧ ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ e ⊆ C.J p q) ∧
      (∀ e ∈ C.edgeSet, ∀ e' ∈ C.edgeSet, e ≠ e' → Disjoint e e') ∧
      (C.vertexSet S).Finite ∧ C.edgeSet.Finite ∧
      (C.vertexSet S).ncard ≤ 2 * S.card ∧ C.edgeSet.ncard ≤ 3 * S.card := by
  classical
  have hgraph : IsFinitePlaneGraph (C.vertexSet S) C.edgeSet := isFinitePlaneGraph hadm
  have hunion : C.vertexSet S ∪ ⋃₀ C.edgeSet = C.V S := V_eq_vertexSet_union_edges.symm
  refine ⟨V_eq_vertexSet_union_edges, hgraph.vtx_disjoint, ?_, hgraph.edge_disjoint,
    hgraph.vtx_finite, hgraph.edge_finite, ?_⟩
  · -- each edge is connected and lies on a single bisecting curve
    rintro e he
    refine ⟨hgraph.edge_isConnected e he, ?_⟩
    obtain ⟨z, hz, rfl⟩ := he
    obtain ⟨p, hp, q, hq, hpq, hsub⟩ := connectedComponentIn_subset_BPair hadm hz
    exact ⟨p, hp, q, hq, hpq, hsub.trans (BPair_subset_J hp hq hpq)⟩
  · -- the `O(n)` count, from the Euler formula for plane graphs
    have hfaces_finite : (faceSet (C.vertexSet S ∪ ⋃₀ C.edgeSet)).Finite := by
      rw [hunion]
      exact faceSet_V_finite hadm
    have hfaces_card : (faceSet (C.vertexSet S ∪ ⋃₀ C.edgeSet)).ncard ≤ S.card := by
      rw [hunion]
      exact faceSet_V_ncard_le hadm
    -- (i) the degree condition at a Voronoi vertex: at least three edges end there
    have hdegree_edges : ∀ v ∈ C.vertexSet S, 3 ≤ {e ∈ C.edgeSet | v ∈ closure e}.ncard :=
      fun v hv => three_le_edges_at_vertex hadm hv
    -- (ii) Euler's inequality for plane graphs (`hEuler`), the one statement assumed here
    obtain ⟨hv, he⟩ := hgraph.ncard_le_of_degree hfaces_finite hdegree_edges hEuler
    exact ⟨hv.trans (Nat.mul_le_mul_left 2 hfaces_card),
      he.trans (Nat.mul_le_mul_left 3 hfaces_card)⟩

end CurveSystem

end AVD
