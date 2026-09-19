import AbstractVoronoi.Jordan.SmallDomain

/-!
# Elementary plane-topology tools

A handful of general facts about the plane used in the proof of the local part of Theorem 4
of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- A point of an open set is accessible from it: a small straight segment ending at the
point does the job. -/
theorem accessibleFrom_of_mem {R : Set Plane} (hR : IsOpen R) {x : Plane} (hx : x ∈ R) :
    AccessibleFrom R x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hR x hx
  set v : Plane := (r / 2) • (EuclideanSpace.single 0 1 : Plane) with hv
  have hnorm : ‖v‖ = r / 2 := by
    rw [hv, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
  have hvne : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    linarith
  refine ⟨fun t => x + (1 - t) • v, ⟨by fun_prop, ?_⟩, by simp, ?_⟩
  · intro s _ t _ hst
    have hv' : (1 - s) • v = (1 - t) • v := by
      have := hst
      simpa using this
    have hzero : ((1 - s) - (1 - t)) • v = 0 := by rw [sub_smul, hv', sub_self]
    rcases smul_eq_zero.1 hzero with h | h
    · linarith [sub_eq_zero.1 (by linarith : (1 - s) - (1 - t) = 0)]
    · exact absurd h hvne
  · rintro y ⟨t, ht, rfl⟩
    refine hball ?_
    rw [mem_ball, dist_eq_norm, show x + (1 - t) • v - x = (1 - t) • v by abel,
      norm_smul, hnorm, Real.norm_eq_abs]
    have h1 : |1 - t| ≤ 1 := by
      rw [abs_le]
      constructor <;> [linarith [ht.2]; linarith [ht.1]]
    nlinarith

/-- The complement of an arc is preconnected: a simple arc does not separate the plane
(`AVD.exists_arc_avoiding_arc`). -/
theorem isPreconnected_compl_arc {κ : ℝ → Plane} (hκ : IsArc κ) :
    IsPreconnected (κ '' Icc 0 1)ᶜ := by
  have harc : Schoenflies.IsArc (κ '' Icc 0 1) := hκ.isArc_image
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  by_cases hxy : x = y
  · exact ⟨{x}, by simpa using hx, rfl, by simp [hxy], isPreconnected_singleton⟩
  · obtain ⟨γ, hγ, h0, h1, hdisj⟩ := exists_arc_avoiding_arc harc hx hy hxy
    refine ⟨γ '' Icc 0 1, ?_, ⟨0, ⟨le_refl 0, zero_le_one⟩, h0⟩,
      ⟨1, ⟨zero_le_one, le_refl 1⟩, h1⟩, ?_⟩
    · intro w hw
      exact fun hc => (Set.disjoint_left.1 hdisj) hc hw
    · exact (isPreconnected_Icc).image γ hγ.cont

/-- The frontier of a connected component of an open set is contained in the frontier of
that set. -/
theorem frontier_connectedComponentIn_subset {U : Set Plane} (hU : IsOpen U) {x : Plane} :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  set V := connectedComponentIn U x with hV
  have hVopen : IsOpen V := hU.connectedComponentIn
  have hVU : V ⊆ U := connectedComponentIn_subset U x
  intro y hy
  have hycl : y ∈ closure V := hy.1
  have hyV : y ∉ V := by
    have := hy.2
    rwa [hVopen.interior_eq] at this
  have hyU : y ∉ U := by
    intro hyU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU y hyU
    obtain ⟨w, hwV, hwball⟩ := Metric.mem_closure_iff.1 hycl r hr
    have hxU : x ∈ U := connectedComponentIn_nonempty_iff.1 ⟨w, hwV⟩
    have hconn : IsPreconnected (V ∪ ball y r) :=
      IsPreconnected.union w hwV (by rwa [mem_ball, dist_comm]) isPreconnected_connectedComponentIn
        isPreconnected_ball
    have hsub : V ∪ ball y r ⊆ V :=
      hconn.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hxU))
        (union_subset hVU hball)
    exact hyV (hsub (Or.inr (mem_ball_self hr)))
  exact ⟨closure_mono hVU hycl, fun hc => hyU (interior_subset hc)⟩

/-- **A connected open set is one of the two complementary domains of its frontier.**

If `D₁` and `D₂` are two disjoint connected open sets whose union is the complement of a set
`C`, and if `U` is a non-empty connected open set with `frontier U = C`, then `U` is `D₁` or
`D₂`.

This identifies the neighbourhoods `U` produced by the local part of Theorem 4 of
Klein–Langetepe–Nilforoushan (2009) as complementary domains of the closed Jordan curve
`frontier U`, which is the form in which the crosscut theorem `AVD.exists_crosscut_domains`
uses them. -/
theorem eq_domain_of_frontier_eq {U C D₁ D₂ : Set Plane} (hU : IsOpen U)
    (hUconn : IsPreconnected U) (hUne : U.Nonempty) (hfr : frontier U = C)
    (h1 : IsOpen D₁) (h2 : IsOpen D₂) (h1c : IsPreconnected D₁) (h2c : IsPreconnected D₂)
    (hdisj : Disjoint D₁ D₂) (hunion : D₁ ∪ D₂ = Cᶜ) : U = D₁ ∨ U = D₂ := by
  have hUC : ∀ x ∈ U, x ∉ C := by
    intro x hx hxC
    rw [← hfr] at hxC
    exact hxC.2 (by rwa [hU.interior_eq])
  have hcover : U ⊆ D₁ ∪ D₂ := by
    intro x hx
    rw [hunion]
    exact hUC x hx
  -- the closure of `U` adds only points of `C`
  have hclU : closure U ⊆ U ∪ C := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · refine Or.inr ?_
      rw [← hfr]
      exact ⟨hx, by rwa [hU.interior_eq]⟩
  have hkey : ∀ D : Set Plane, IsPreconnected D → (∀ x ∈ D, x ∉ C) → U ⊆ D → U = D := by
    intro D hDconn hDC hUD
    refine Subset.antisymm hUD ?_
    have hDcover : D ⊆ U ∪ (closure U)ᶜ := by
      intro x hx
      by_cases hxcl : x ∈ closure U
      · rcases hclU hxcl with h | h
        · exact Or.inl h
        · exact absurd h (hDC x hx)
      · exact Or.inr hxcl
    have hdis : Disjoint U ((closure U)ᶜ) :=
      Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
    obtain ⟨x, hxU⟩ := hUne
    rcases hDconn.subset_or_subset hU isClosed_closure.isOpen_compl hdis hDcover with h | h
    · exact h
    · exact absurd (h (hUD hxU)) (fun hc => hc (subset_closure hxU))
  have hDC : ∀ D : Set Plane, D ⊆ Cᶜ → ∀ x ∈ D, x ∉ C := fun D hD x hx => hD hx
  have h1C : D₁ ⊆ Cᶜ := by rw [← hunion]; exact subset_union_left
  have h2C : D₂ ⊆ Cᶜ := by rw [← hunion]; exact subset_union_right
  rcases hUconn.subset_or_subset h1 h2 hdisj hcover with h | h
  · exact Or.inl (hkey D₁ h1c (hDC D₁ h1C) h)
  · exact Or.inr (hkey D₂ h2c (hDC D₂ h2C) h)

/-- A preconnected set disjoint from the frontier of `T` and containing a point outside the
closure of `T` is disjoint from `T`. -/
theorem disjoint_of_preconnected_of_disjoint_frontier {S T : Set Plane}
    (hS : IsPreconnected S) (hdisj : Disjoint S (frontier T)) {x : Plane} (hxS : x ∈ S)
    (hxT : x ∉ closure T) : Disjoint S T := by
  have hcover : S ⊆ interior T ∪ (closure T)ᶜ := by
    intro w hw
    by_cases h : w ∈ closure T
    · refine Or.inl ?_
      by_contra hc
      exact (Set.disjoint_left.1 hdisj) hw ⟨h, hc⟩
    · exact Or.inr h
  have hdis : Disjoint (interior T) ((closure T)ᶜ) :=
    Set.disjoint_left.2 fun u hu hu' => hu' (interior_subset.trans subset_closure hu)
  have hright := hS.subset_right_of_subset_union isOpen_interior
    isClosed_closure.isOpen_compl hdis hcover ⟨x, hxS, hxT⟩
  exact Set.disjoint_left.2 fun u hu hu' => (hright hu) (subset_closure hu')

end AVD
