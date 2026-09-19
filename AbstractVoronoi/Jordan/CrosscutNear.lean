import AbstractVoronoi.Jordan.PlaneTools

/-!
# Crosscuts with prescribed endpoints, of arbitrarily small diameter

This file contains one construction, `AVD.exists_crosscut_near`: if an open plane set `D`
with frontier `C` is locally connected at the points of `C`, then any two points of `C`
close enough to a given point `z ∈ C` are the endpoints of a crosscut of `D` running inside
a prescribed ball around `z`.

This is the ingredient which makes the neighbourhoods `U` of the local part of Theorem 4 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

small, in `AbstractVoronoi.Jordan.LocalAccessibility`.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- **Crosscuts with prescribed endpoints, of arbitrarily small diameter.**

If the open set `D` has frontier `C` and is locally connected at every point of `C`, then
for every `z ∈ C` and every `ε > 0` there is a `δ > 0` such that any two distinct points
`a, b` of `C` at distance less than `δ` from `z` are the endpoints of an arc whose relative
interior runs inside `D ∩ ball z ε`.

The arc is assembled, as in the three "Facts" of the proof of Lemma 6 of
Klein–Langetepe–Nilforoushan (2009), from an access arc of `a`, an access arc of `b` and a
connection between their starting points (`AVD.exists_arc_of_accessible`); the access arcs
are small because `D` is locally connected at `a` and at `b`
(`AVD.exists_locally_connected_nbhd`), and the connection is small because `D` is locally
connected at `z`. -/
theorem exists_crosscut_near {D C : Set Plane} (hDo : IsOpen D) (hfrD : frontier D = C)
    (hlc : ∀ y ∈ C, LocallyConnectedAt D y) {z : Plane} (hz : z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ C, ∀ b ∈ C, dist a z < δ → dist b z < δ → a ≠ b →
      ∃ κ : ℝ → Plane, IsArc κ ∧ κ 0 = a ∧ κ 1 = b ∧ κ '' Ioo 0 1 ⊆ D ∩ ball z ε := by
  have hDC : Disjoint D C := by
    rw [← hfrD, hDo.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  obtain ⟨δ₀, hδ₀, hjoin⟩ := hlc z hz ε hε
  set m : ℝ := min δ₀ ε with hm
  have hmpos : 0 < m := lt_min hδ₀ hε
  -- a small access neighbourhood at every point of the curve close to `z`
  have key : ∀ w ∈ C, dist w z < m / 2 → ∃ V : Set Plane, IsOpen V ∧ IsPreconnected V ∧
      V.Nonempty ∧ V ⊆ D ∧ V ⊆ ball z m ∧ ∀ x ∈ V, AccessibleWithin V x w := by
    intro w hw hwd
    have hwD : w ∉ D := fun h => (Set.disjoint_left.1 hDC) h hw
    have hwc : w ∈ closure D := by
      rw [← hfrD] at hw; exact frontier_subset_closure hw
    obtain ⟨V, δ, hVo, hVc, hVne, hVD, hVball, -, -, -, hacc⟩ :=
      exists_locally_connected_nbhd hDo hwD hwc (hlc w hw)
        (show 0 < m / 2 - dist w z by linarith)
    refine ⟨V, hVo, hVc, hVne, hVD, ?_, hacc⟩
    intro u hu
    have hub := hVball hu
    rw [mem_ball] at hub ⊢
    calc dist u z ≤ dist u w + dist w z := dist_triangle u w z
      _ < (m / 2 - dist w z) + dist w z := by linarith
      _ = m / 2 := by ring
      _ < m := by linarith
  refine ⟨m / 2, by linarith, ?_⟩
  intro a ha b hb hda hdb hab
  obtain ⟨Va, hVao, hVac, ⟨p, hp⟩, hVaD, hVaball, hacca⟩ := key a ha hda
  obtain ⟨Vb, hVbo, hVbc, ⟨q, hq⟩, hVbD, hVbball, haccb⟩ := key b hb hdb
  have hmε : m ≤ ε := min_le_right _ _
  have hmδ : m ≤ δ₀ := min_le_left _ _
  have hpmem : p ∈ D ∩ ball z ε := ⟨hVaD hp, ball_subset_ball hmε (hVaball hp)⟩
  have hqmem : q ∈ D ∩ ball z ε := ⟨hVbD hq, ball_subset_ball hmε (hVbball hq)⟩
  have hjoined : JoinedIn (D ∩ ball z ε) p q :=
    hjoin p ⟨hVaD hp, ball_subset_ball hmδ (hVaball hp)⟩ q
      ⟨hVbD hq, ball_subset_ball hmδ (hVbball hq)⟩
  set R : Set Plane := connectedComponentIn (D ∩ ball z ε) p with hR
  have hRopen : IsOpen R := (hDo.inter isOpen_ball).connectedComponentIn
  have hRsub : R ⊆ D ∩ ball z ε := connectedComponentIn_subset _ _
  have hpR : p ∈ R := mem_connectedComponentIn hpmem
  have hqR : q ∈ R := mem_connectedComponentIn_of_joinedIn hjoined
  have hVaR : Va ⊆ R :=
    hVac.subset_connectedComponentIn hp
      (fun u hu => ⟨hVaD hu, ball_subset_ball hmε (hVaball hu)⟩)
  have hVbR : Vb ⊆ R := by
    have hsub : Vb ⊆ D ∩ ball z ε :=
      fun u hu => ⟨hVbD hu, ball_subset_ball hmε (hVbball hu)⟩
    have := hVbc.subset_connectedComponentIn hq hsub
    rwa [← connectedComponentIn_eq hqR] at this
  have hRconn : ∀ x ∈ R, ∀ y ∈ R, JoinedIn R x y := by
    have hcR : IsConnected R := ⟨⟨p, hpR⟩, isPreconnected_connectedComponentIn⟩
    have := (hRopen.isConnected_iff_isPathConnected).1 hcR
    exact fun x hx y hy => this.joinedIn x hx y hy
  have haccA : AccessibleFrom R a :=
    AccessibleFrom.mono hVaR (AccessibleFrom.of_within (hacca p hp))
  have haccB : AccessibleFrom R b :=
    AccessibleFrom.mono hVbR (AccessibleFrom.of_within (haccb q hq))
  obtain ⟨κ, hκ, h0, h1, hsub⟩ := exists_arc_of_accessible hRopen hRconn hab haccA haccB
  exact ⟨κ, hκ, h0, h1, hsub.trans hRsub⟩

end AVD
