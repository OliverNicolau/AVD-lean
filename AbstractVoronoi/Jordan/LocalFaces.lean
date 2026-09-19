import AbstractVoronoi.Jordan.PlaneGraph

/-!
# How many faces can meet at a point of a plane set

This file proves the *local* half of the degree condition used by the Euler count in the
proof of **Theorem 10** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

The paper asserts, as a classical fact of plane topology, that a vertex of a plane graph
lying on the closures of at least three faces is an end of at least three edges.  Its
contrapositive form is a statement about how a *small piece* of the graph can separate a
neighbourhood of the vertex, and the case in which that piece lies on a single Jordan curve
is proved here:

`AVD.faces_at_ncard_le_two_of_local_subset_jordan` — if a closed set `G` of the plane agrees,
inside some neighbourhood `U` of a point `z`, with a subset of a Jordan curve `J` through `z`
(and `U` is one of the neighbourhoods supplied by Theorem 4, so that `U ∩ D₁` and `U ∩ D₂`
are connected, where `D₁, D₂` are the two complementary domains of `J`), then at most **two**
faces of `G` have `z` in their closure.

The proof is the two-case argument one draws on a picture.  Either the whole of `J ∩ U`
belongs to `G`, and then `U \ G = (U ∩ D₁) ∪ (U ∩ D₂)` consists of two connected pieces, each
of which lies in a single face; or some point `x` of `J ∩ U` is *not* in `G`, and then a small
disc around `x` lies in the complement of `G` and meets both `D₁` and `D₂`, so that the two
pieces are joined through it and `U \ G` is connected — a single face.

The faces of `G` are the connected components of `Gᶜ` (`AVD.faceSet`), so the counting step is
the observation that a connected subset of `Gᶜ` lies inside one single face
(`AVD.face_eq_of_isPreconnected`).
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- A connected subset of the complement of `G` meets at most one face of `G`, and determines
it: if a face `F` of `G` contains a point `y` of a preconnected set `A ⊆ Gᶜ`, then `F` is the
connected component of `Gᶜ` of *every* point `a` of `A`. -/
theorem face_eq_of_isPreconnected {G A : Set Plane} (hA : IsPreconnected A) (hAG : A ⊆ Gᶜ)
    {F : Set Plane} (hF : F ∈ faceSet G) {y : Plane} (hyF : y ∈ F) (hyA : y ∈ A)
    {a : Plane} (ha : a ∈ A) : F = connectedComponentIn Gᶜ a := by
  obtain ⟨w, -, rfl⟩ := hF
  have hy : connectedComponentIn Gᶜ w = connectedComponentIn Gᶜ y := connectedComponentIn_eq hyF
  have hsub : A ⊆ connectedComponentIn Gᶜ y := hA.subset_connectedComponentIn hyA hAG
  rw [hy, connectedComponentIn_eq (hsub ha)]

/-- Every face of `G` whose closure contains `z` meets every neighbourhood of `z`. -/
theorem exists_mem_face_inter_of_mem_closure {G U F : Set Plane} {z : Plane}
    (hUopen : IsOpen U) (hzU : z ∈ U) (hF : F ∈ faceSet G) (hzF : z ∈ closure F) :
    ∃ y ∈ F, y ∈ U ∧ y ∉ G := by
  obtain ⟨y, hyU, hyF⟩ := mem_closure_iff.1 hzF U hUopen hzU
  refine ⟨y, hyF, hyU, ?_⟩
  obtain ⟨w, -, rfl⟩ := hF
  exact connectedComponentIn_subset _ _ hyF

/-- **At most two faces can meet at a point where the set lies on a single Jordan curve.**

Let `G` be a closed subset of the plane, let `J` be a curve whose complement is the union of
the two disjoint open domains `D₁`, `D₂`, each having `J` as its frontier — the conclusion of
the global part of **Theorem 4** of Klein–Langetepe–Nilforoushan (2009) — and let `U` be a
neighbourhood of a point `z` such that `U ∩ D₁` and `U ∩ D₂` are connected, as provided by
the local part of Theorem 4.  If inside `U` the set `G` is contained in `J`, then the faces
of `G` (the connected components of `Gᶜ`, `AVD.faceSet`) whose closures contain `z` are at
most two.

This is the local statement behind the degree condition of the Euler count in the proof of
**Theorem 10**: three faces meeting at a point cannot be separated near it by a piece of a
single curve. -/
theorem faces_at_subset_pair_of_local_subset_jordan {G J D₁ D₂ U : Set Plane} {z : Plane}
    (hGclosed : IsClosed G) (hunion : D₁ ∪ D₂ = Jᶜ)
    (hf1 : frontier D₁ = J) (hf2 : frontier D₂ = J)
    (hUopen : IsOpen U) (hzU : z ∈ U)
    (hc1 : IsConnected (U ∩ D₁)) (hc2 : IsConnected (U ∩ D₂))
    (hGU : G ∩ U ⊆ J) :
    ∃ F₁ F₂ : Set Plane, {F ∈ faceSet G | z ∈ closure F} ⊆ {F₁, F₂} := by
  have hD1J : D₁ ⊆ Jᶜ := hunion ▸ subset_union_left
  have hD2J : D₂ ⊆ Jᶜ := hunion ▸ subset_union_right
  -- inside `U`, the two domains avoid `G`
  have hUD1G : U ∩ D₁ ⊆ Gᶜ := by
    rintro x ⟨hxU, hxD⟩ hxG
    exact hD1J hxD (hGU ⟨hxG, hxU⟩)
  have hUD2G : U ∩ D₂ ⊆ Gᶜ := by
    rintro x ⟨hxU, hxD⟩ hxG
    exact hD2J hxD (hGU ⟨hxG, hxU⟩)
  by_cases hcase : J ∩ U ⊆ G
  case neg =>
    -- some point of the curve inside `U` is off `G`: the complement of `G` in `U` is connected
    obtain ⟨x, ⟨hxJ, hxU⟩, hxG⟩ := Set.not_subset.1 hcase
    have hUGopen : IsOpen (U \ G) := hUopen.sdiff hGclosed
    -- around any point of `U \ G` on the curve there is a ball inside `U \ G` meeting both
    -- domains
    have hball : ∀ y ∈ U \ G, y ∈ J → ∃ ε > 0, ball y ε ⊆ U \ G ∧
        (ball y ε ∩ (U ∩ D₁)).Nonempty ∧ (ball y ε ∩ (U ∩ D₂)).Nonempty := by
      intro y hy hyJ
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUGopen y hy
      have hy1 : y ∈ closure D₁ := by
        rw [← hf1] at hyJ; exact frontier_subset_closure hyJ
      have hy2 : y ∈ closure D₂ := by
        rw [← hf2] at hyJ; exact frontier_subset_closure hyJ
      obtain ⟨a, ha1, ha2⟩ := mem_closure_iff.1 hy1 (ball y ε) isOpen_ball (mem_ball_self hε)
      obtain ⟨b, hb1, hb2⟩ := mem_closure_iff.1 hy2 (ball y ε) isOpen_ball (mem_ball_self hε)
      exact ⟨ε, hε, hball, ⟨a, ha1, (hball ha1).1, ha2⟩, ⟨b, hb1, (hball hb1).1, hb2⟩⟩
    obtain ⟨ε, hε, hballsub, ⟨a, haball, haU⟩, ⟨b, hbball, hbU⟩⟩ :=
      hball x ⟨hxU, hxG⟩ hxJ
    -- the "core" connected set: the ball around `x` together with the two half-neighbourhoods
    set W : Set Plane := (ball x ε ∪ (U ∩ D₁)) ∪ (U ∩ D₂) with hW
    have hWsub : W ⊆ U \ G := by
      rintro y ((hy | hy) | hy)
      · exact hballsub hy
      · exact ⟨hy.1, hUD1G hy⟩
      · exact ⟨hy.1, hUD2G hy⟩
    have hWconn : IsPreconnected W := by
      have h1 : IsPreconnected (ball x ε ∪ (U ∩ D₁)) :=
        IsPreconnected.union a haball haU (convex_ball x ε).isPreconnected hc1.isPreconnected
      exact IsPreconnected.union b (Or.inl hbball) hbU h1 hc2.isPreconnected
    have hxW : x ∈ W := Or.inl (Or.inl (mem_ball_self hε))
    have hconn : IsPreconnected (U \ G) := by
      refine isPreconnected_of_forall x fun y hy => ?_
      by_cases hyJ : y ∈ J
      · obtain ⟨δ, hδ, hδsub, ⟨c, hcball, hcU⟩, -⟩ := hball y hy hyJ
        refine ⟨ball y δ ∪ W, ?_, Or.inr hxW, Or.inl (mem_ball_self hδ), ?_⟩
        · exact union_subset hδsub hWsub
        · exact IsPreconnected.union c hcball (Or.inl (Or.inr hcU))
            (convex_ball y δ).isPreconnected hWconn
      · have : y ∈ D₁ ∪ D₂ := by rw [hunion]; exact hyJ
        refine ⟨W, hWsub, hxW, ?_, hWconn⟩
        rcases this with h | h
        · exact Or.inl (Or.inr ⟨hy.1, h⟩)
        · exact Or.inr ⟨hy.1, h⟩
    refine ⟨connectedComponentIn Gᶜ x, connectedComponentIn Gᶜ x, ?_⟩
    rintro F ⟨hF, hzF⟩
    obtain ⟨y, hyF, hyU, hyG⟩ := exists_mem_face_inter_of_mem_closure hUopen hzU hF hzF
    have hAG : U \ G ⊆ Gᶜ := fun w hw => hw.2
    exact Or.inl (face_eq_of_isPreconnected hconn hAG hF hyF ⟨hyU, hyG⟩ ⟨hxU, hxG⟩)
  case pos =>
    -- the curve inside `U` lies entirely in `G`: only the two half-neighbourhoods are left
    obtain ⟨x₁, hx₁⟩ := hc1.nonempty
    obtain ⟨x₂, hx₂⟩ := hc2.nonempty
    refine ⟨connectedComponentIn Gᶜ x₁, connectedComponentIn Gᶜ x₂, ?_⟩
    rintro F ⟨hF, hzF⟩
    obtain ⟨y, hyF, hyU, hyG⟩ := exists_mem_face_inter_of_mem_closure hUopen hzU hF hzF
    have hyJ : y ∉ J := fun h => hyG (hcase ⟨h, hyU⟩)
    have : y ∈ D₁ ∪ D₂ := by rw [hunion]; exact hyJ
    rcases this with h | h
    · exact Or.inl (face_eq_of_isPreconnected hc1.isPreconnected hUD1G hF hyF ⟨hyU, h⟩ hx₁)
    · exact Or.inr (face_eq_of_isPreconnected hc2.isPreconnected hUD2G hF hyF ⟨hyU, h⟩ hx₂)

/-- The counting form of `AVD.faces_at_subset_pair_of_local_subset_jordan`: at most two faces
of `G` have `z` in their closure, when `G` agrees near `z` with a subset of a single Jordan
curve through `z`. -/
theorem faces_at_ncard_le_two_of_local_subset_jordan {G J D₁ D₂ U : Set Plane} {z : Plane}
    (hGclosed : IsClosed G) (hunion : D₁ ∪ D₂ = Jᶜ)
    (hf1 : frontier D₁ = J) (hf2 : frontier D₂ = J)
    (hUopen : IsOpen U) (hzU : z ∈ U)
    (hc1 : IsConnected (U ∩ D₁)) (hc2 : IsConnected (U ∩ D₂))
    (hGU : G ∩ U ⊆ J) :
    {F ∈ faceSet G | z ∈ closure F}.ncard ≤ 2 := by
  obtain ⟨F₁, F₂, hsub⟩ := faces_at_subset_pair_of_local_subset_jordan hGclosed hunion hf1 hf2
    hUopen hzU hc1 hc2 hGU
  calc {F ∈ faceSet G | z ∈ closure F}.ncard
      ≤ ({F₁, F₂} : Set (Set Plane)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
        apply le_trans (Set.ncard_insert_le _ _)
        simp

end AVD
