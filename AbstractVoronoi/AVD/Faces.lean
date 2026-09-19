import AbstractVoronoi.AVD.Edges
import AbstractVoronoi.Jordan.PlaneGraph

/-!
# The faces of a Voronoi diagram

The complement of the Voronoi diagram `V(S)` is the union of the Voronoi regions, and by
axiom `A₂` each region is path-connected; the regions of distinct sites being disjoint and
open, the non-empty ones are exactly the connected components of the complement, that is, the
**faces** of the plane graph `V(S)` in the sense of `AVD.faceSet`.

This is the step of the proof of **Theorem 10** of Klein–Langetepe–Nilforoushan (2009) that
supplies the bound "at most `n` faces" to the Euler count:

> The Voronoi diagram `V(S)` is a planar graph whose faces are the Voronoi regions.

The main results are `AVD.CurveSystem.faceSet_V_eq` (the faces are the non-empty regions),
`AVD.CurveSystem.faceSet_V_ncard_le` (there are at most `n` of them) and
`AVD.CurveSystem.three_le_faces_at_vertex` (a Voronoi vertex lies on the closures of at least
three faces), which is the degree condition of the Euler count.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- The complement of the Voronoi diagram is the union of the Voronoi regions. -/
theorem compl_V_eq : (C.V S)ᶜ = ⋃ p ∈ S, C.VR p S := by
  rw [V, compl_compl]

/-- Each Voronoi region is path-connected, by axiom `A₂` of Definition 1. -/
theorem VR_isPathConnected (hadm : C.Admissible) {p : ι} {S' : Finset ι} (hS' : S' ⊆ S)
    (hp : p ∈ S') (hne : (C.VR p S').Nonempty) : IsPathConnected (C.VR p S') := by
  refine isPathConnected_iff.2 ⟨hne, fun x hx y hy => hadm.A2 S' hS' p hp x hx y hy⟩

/-- A non-empty Voronoi region is a connected component of the complement of the diagram:
it is open, connected, and separated from the other regions. -/
theorem connectedComponentIn_compl_V_eq (hadm : C.Admissible) {p : ι} (hp : p ∈ S)
    {z : Plane} (hz : z ∈ C.VR p S) : connectedComponentIn (C.V S)ᶜ z = C.VR p S := by
  classical
  have hzc : z ∈ (C.V S)ᶜ := by
    rw [compl_V_eq]
    exact mem_biUnion hp hz
  have hVRopen : IsOpen (C.VR p S) := VR_isOpen Subset.rfl hp
  have hVRconn : IsPreconnected (C.VR p S) :=
    (VR_isPathConnected hadm Subset.rfl hp ⟨z, hz⟩).isConnected.isPreconnected
  have hsub : C.VR p S ⊆ (C.V S)ᶜ := by
    rw [compl_V_eq]
    exact fun x hx => mem_biUnion hp hx
  -- the union of the other regions is an open set, disjoint from `VR p S`
  set W : Set Plane := ⋃ q ∈ S.erase p, C.VR q S with hWdef
  have hWopen : IsOpen W := isOpen_biUnion fun q hq =>
    VR_isOpen Subset.rfl (Finset.mem_of_mem_erase hq)
  have hWdisj : Disjoint (C.VR p S) W := by
    rw [hWdef, disjoint_iUnion₂_right]
    intro q hq
    exact VR_disjoint Subset.rfl hp (Finset.mem_of_mem_erase hq)
      (Finset.ne_of_mem_erase hq).symm
  have hcover : (C.V S)ᶜ ⊆ C.VR p S ∪ W := by
    rw [compl_V_eq]
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hx
    rcases eq_or_ne q p with rfl | hqp
    · exact Or.inl hxq
    · exact Or.inr (mem_biUnion (Finset.mem_erase.2 ⟨hqp, hq⟩) hxq)
  refine Subset.antisymm ?_ (hVRconn.subset_connectedComponentIn hz hsub)
  -- the component of `z` cannot meet the other regions
  have hKconn : IsPreconnected (connectedComponentIn (C.V S)ᶜ z) :=
    isPreconnected_connectedComponentIn
  have hKsub : connectedComponentIn (C.V S)ᶜ z ⊆ (C.V S)ᶜ := connectedComponentIn_subset _ _
  intro x hx
  by_contra hxp
  have hxW : x ∈ W := (hcover (hKsub hx)).resolve_left hxp
  obtain ⟨y, hyK, hyp, hyW⟩ :=
    hKconn (C.VR p S) W hVRopen hWopen (hKsub.trans hcover)
      ⟨z, mem_connectedComponentIn hzc, hz⟩ ⟨x, hx, hxW⟩
  exact (hWdisj.le_bot ⟨hyp, hyW⟩).elim

/-- **The faces of the Voronoi diagram are its non-empty Voronoi regions.**  This is the
identification the proof of Theorem 10 of Klein–Langetepe–Nilforoushan (2009) makes when it
counts the faces of the plane graph `V(S)`. -/
theorem faceSet_V_eq (hadm : C.Admissible) :
    faceSet (C.V S) = {F | ∃ p ∈ S, (C.VR p S).Nonempty ∧ F = C.VR p S} := by
  ext F
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [compl_V_eq] at hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    exact ⟨p, hp, ⟨z, hzp⟩, connectedComponentIn_compl_V_eq hadm hp hzp⟩
  · rintro ⟨p, hp, ⟨z, hz⟩, rfl⟩
    refine ⟨z, ?_, (connectedComponentIn_compl_V_eq hadm hp hz).symm⟩
    rw [compl_V_eq]
    exact mem_biUnion hp hz

/-- The Voronoi diagram has at most `n = |S|` faces. -/
theorem faceSet_V_ncard_le (hadm : C.Admissible) : (faceSet (C.V S)).ncard ≤ S.card := by
  classical
  have hsub : faceSet (C.V S) ⊆ (fun p => C.VR p S) '' S := by
    rw [faceSet_V_eq hadm]
    rintro F ⟨p, hp, -, rfl⟩
    exact ⟨p, hp, rfl⟩
  have hfin : ((fun p => C.VR p S) '' S).Finite := S.finite_toSet.image _
  calc (faceSet (C.V S)).ncard ≤ ((fun p => C.VR p S) '' (S : Set ι)).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ (S : Set ι).ncard := Set.ncard_image_le S.finite_toSet
    _ = S.card := by simp

/-- The set of faces of the Voronoi diagram is finite. -/
theorem faceSet_V_finite (hadm : C.Admissible) : (faceSet (C.V S)).Finite := by
  classical
  refine Set.Finite.subset (S.finite_toSet.image fun p => C.VR p S) ?_
  rw [faceSet_V_eq hadm]
  rintro F ⟨p, hp, -, rfl⟩
  exact ⟨p, hp, rfl⟩

/-- **A Voronoi vertex lies on the closures of at least three faces.**  This is the degree
condition of the Euler count in the proof of Theorem 10 of
Klein–Langetepe–Nilforoushan (2009): a point of `B'` lies on the boundaries of three Voronoi
regions, which are three distinct faces of the diagram. -/
theorem three_le_faces_at_vertex (hadm : C.Admissible) {z : Plane} (hz : z ∈ C.vertexSet S) :
    3 ≤ {F ∈ faceSet (C.V S) | z ∈ closure F}.ncard := by
  classical
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, hzp, hzq, hzr⟩ := hz
  -- a point on the frontier of a region lies in its closure, and the region is non-empty
  have hmem : ∀ t ∈ S, z ∈ frontier (C.VR t S) →
      C.VR t S ∈ {F ∈ faceSet (C.V S) | z ∈ closure F} := by
    intro t ht hzt
    have hne : (C.VR t S).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, frontier_empty] at hzt
      exact hzt
    refine ⟨?_, frontier_subset_closure hzt⟩
    rw [faceSet_V_eq hadm]
    exact ⟨t, ht, hne, rfl⟩
  have hnep : (C.VR p S).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, frontier_empty] at hzp
    exact hzp
  have hneq : (C.VR q S).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, frontier_empty] at hzq
    exact hzq
  have hner : (C.VR r S).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, frontier_empty] at hzr
    exact hzr
  -- distinct sites have distinct (disjoint, non-empty) regions
  have hdist : ∀ s t : ι, s ∈ S → t ∈ S → s ≠ t → (C.VR s S).Nonempty →
      C.VR s S ≠ C.VR t S := by
    intro s t hs ht hst hnes heq
    obtain ⟨x, hx⟩ := hnes
    have hxt : x ∈ C.VR t S := by rw [← heq]; exact hx
    exact (VR_disjoint Subset.rfl hs ht hst).le_bot ⟨hx, hxt⟩
  have htriple : ({C.VR p S, C.VR q S, C.VR r S} : Set (Set Plane)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨C.VR p S, C.VR q S, C.VR r S, hdist p q hp hq hpq hnep,
      hdist p r hp hr hpr hnep, hdist q r hq hr hqr hneq, rfl⟩
  have hsub : ({C.VR p S, C.VR q S, C.VR r S} : Set (Set Plane)) ⊆
      {F ∈ faceSet (C.V S) | z ∈ closure F} := by
    rintro F (rfl | rfl | rfl)
    · exact hmem p hp hzp
    · exact hmem q hq hzq
    · exact hmem r hr hzr
  have hfin : {F ∈ faceSet (C.V S) | z ∈ closure F}.Finite :=
    (faceSet_V_finite hadm).subset fun F hF => hF.1
  calc (3 : ℕ) = ({C.VR p S, C.VR q S, C.VR r S} : Set (Set Plane)).ncard := htriple.symm
    _ ≤ {F ∈ faceSet (C.V S) | z ∈ closure F}.ncard := Set.ncard_le_ncard hsub hfin

/-- The Voronoi diagram is a closed subset of the plane: its complement is the union of the
open Voronoi regions. -/
theorem isClosed_V : IsClosed (C.V S) := by
  rw [← isOpen_compl_iff, compl_V_eq]
  exact isOpen_biUnion fun p hp => VR_isOpen Subset.rfl hp

/-- The Voronoi diagram is the union of its vertices and of its edges: every point of the
diagram is either a Voronoi vertex or lies on the connected component of the remainder that
contains it.  This is the first assertion of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009). -/
theorem V_eq_vertexSet_union_edges :
    C.V S = C.vertexSet S ∪ ⋃₀ C.edgeSet := by
  apply Subset.antisymm
  · intro z hz
    by_cases hzv : z ∈ C.vertexSet S
    · exact Or.inl hzv
    · exact Or.inr ⟨connectedComponentIn (C.V S \ C.vertexSet S) z, ⟨z, ⟨hz, hzv⟩, rfl⟩,
        mem_connectedComponentIn ⟨hz, hzv⟩⟩
  · rintro z (hz | ⟨e, ⟨z₀, hz₀, rfl⟩, hze⟩)
    · exact vertexSet_subset_V hz
    · exact (connectedComponentIn_subset _ z₀ hze).1

/-- **The Voronoi diagram is a finite plane graph** in the sense of
`AVD.IsFinitePlaneGraph`: its vertices are the points lying on at least three region
boundaries, its edges are the connected components of the rest of the diagram, each edge is
an open subarc of a bisecting curve whose ends are vertices, and there are finitely many of
each.  This packages the assertions of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009) in the form in which the Euler count is applied. -/
theorem isFinitePlaneGraph (hadm : C.Admissible) :
    IsFinitePlaneGraph (C.vertexSet S) C.edgeSet where
  vtx_finite := vertexSet_finite hadm
  edge_finite := edgeSet_finite hadm
  edge_isConnected := by
    rintro e ⟨z, hz, rfl⟩
    exact isConnected_connectedComponentIn_iff.2 hz
  edge_disjoint := by
    rintro e ⟨z, hz, rfl⟩ e' ⟨z', hz', rfl⟩ hne
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    exact hne ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hx').symm)
  vtx_disjoint := by
    refine Set.disjoint_left.2 ?_
    rintro z hz ⟨e, ⟨z₀, hz₀, rfl⟩, hze⟩
    exact (connectedComponentIn_subset _ z₀ hze).2 hz
  edge_isArc := fun e he => (edge_isSubarc_and_ends hadm he).1
  edge_ends := fun e he => (edge_isSubarc_and_ends hadm he).2
  isClosed := by
    rw [← V_eq_vertexSet_union_edges]
    exact isClosed_V

end CurveSystem

end AVD
