import AbstractVoronoi.Jordan.LocalAccessibility

/-!
# The local part of Theorem 4 for the unbounded curves of axiom `A₁`

The construction of `AbstractVoronoi.Jordan.LocalAccessibility` is local: the only global input it
needs is a *bounded* domain `Ω ⊆ D` cut off by a crosscut `k` of `D` along a small arc `g` of
the curve, that is, a domain with `frontier Ω = k ∪ g`.  For a closed Jordan curve this is
the crosscut theorem; for the unbounded curves of axiom `A₁` of Definition 1 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

it is obtained here directly from the Jordan curve theorem applied to the closed Jordan
curve `k ∪ g`: the complement of the small arc in the curve is covered by *unbounded*
connected pieces, which therefore lie in the unbounded complementary domain of `k ∪ g`, so
that the bounded one avoids the curve altogether and, being connected and adjacent to the
relative interior of `k`, lies inside `D`.

This yields the local part of Theorem 4 for the unbounded curves as well
(`AVD.IsUnboundedJordanCurve.exists_local_nbhd`).
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- The plane contains points at arbitrarily large distance from a given point. -/
theorem exists_dist_gt (z : Plane) (r : ℝ) : ∃ y : Plane, r < dist y z := by
  refine ⟨z + (|r| + 1) • (EuclideanSpace.single 0 1 : Plane), ?_⟩
  have h : dist (z + (|r| + 1) • (EuclideanSpace.single 0 1 : Plane)) z = |r| + 1 := by
    rw [dist_eq_norm, show z + (|r| + 1) • (EuclideanSpace.single 0 1 : Plane) - z =
      (|r| + 1) • (EuclideanSpace.single 0 1 : Plane) by abel, norm_smul, PiLp.norm_single,
      norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h]
  have := le_abs_self r
  linarith

/-- **The bounded domain cut off by a crosscut**, for a curve whose part outside the
prescribed arc is covered by unbounded connected pieces.

Let `C` be a curve separating the plane into the open sets `D` and `E`, let `g` be an arc of
`C` and let `k` be a crosscut of `D` with the same endpoints as `g`.  If every point of
`C ∖ g` lies on an unbounded connected subset of `C ∖ g` — which is the case both for a
closed Jordan curve, where `C ∖ g` is bounded but then the hypothesis is applied after
exchanging the two arcs, and for a properly embedded line, where `C ∖ g` consists of two
unbounded ends — then the bounded complementary domain `Ω` of the closed Jordan curve
`k ∪ g` is contained in `D` and satisfies `frontier Ω = k ∪ g`.

This is the form of the crosscut theorem used for the unbounded curves of axiom `A₁` of
Klein–Langetepe–Nilforoushan (2009). -/
theorem exists_bounded_crosscut_domain {C D E : Set Plane} {g k : ℝ → Plane}
    (hDo : IsOpen D) (hEo : IsOpen E) (hdisjDE : Disjoint D E) (hunion : D ∪ E = Cᶜ)
    (hg : IsArc g) (hk : IsArc k) (hk0 : k 0 = g 0) (hk1 : k 1 = g 1)
    (hkD : k '' Ioo 0 1 ⊆ D) (hgC : g '' Icc 0 1 ⊆ C)
    (hrest : ∀ x ∈ C \ g '' Icc 0 1, ∃ S : Set Plane, IsPreconnected S ∧ x ∈ S ∧
      S ⊆ C \ g '' Icc 0 1 ∧ ¬ Bornology.IsBounded S) :
    ∃ Ω : Set Plane, IsOpen Ω ∧ IsConnected Ω ∧ Ω ⊆ D ∧ Bornology.IsBounded Ω ∧
      frontier Ω = k '' Icc 0 1 ∪ g '' Icc 0 1 := by
  have hDC : Disjoint D C := by
    refine Set.disjoint_left.2 fun x hx hxC => ?_
    have : x ∈ Cᶜ := by rw [← hunion]; exact Or.inl hx
    exact this hxC
  have hdisjint : Disjoint (k '' Ioo 0 1) (g '' Ioo 0 1) :=
    Set.disjoint_left.2 fun x hx hx' =>
      (Set.disjoint_left.1 hDC) (hkD hx) (hgC (Set.image_mono Ioo_subset_Icc_self hx'))
  have hJ : IsClosedJordanCurve (k '' Icc 0 1 ∪ g '' Icc 0 1) :=
    isClosedJordanCurve_of_arcs hk hg hk0 hk1 hdisjint
  obtain ⟨P, Q, hPo, hQo, hPc, hQc, hPQd, hPQu, hfP, hfQ, hbdd⟩ :=
    hJ.exists_separation_frontier_eq
  -- the bounded complementary domain of `k ∪ g` is the one we want
  have main : ∀ P Q : Set Plane, IsOpen P → IsOpen Q → IsConnected P → Disjoint P Q →
      P ∪ Q = (k '' Icc 0 1 ∪ g '' Icc 0 1)ᶜ →
      frontier P = k '' Icc 0 1 ∪ g '' Icc 0 1 → Bornology.IsBounded P →
      ¬ Bornology.IsBounded Q →
      ∃ Ω : Set Plane, IsOpen Ω ∧ IsConnected Ω ∧ Ω ⊆ D ∧ Bornology.IsBounded Ω ∧
        frontier Ω = k '' Icc 0 1 ∪ g '' Icc 0 1 := by
    intro P Q hPo hQo hPc hPQd hPQu hfP hPb hQu
    have hPJ : Disjoint P (k '' Icc 0 1 ∪ g '' Icc 0 1) := by
      refine Set.disjoint_left.2 fun w hw hw' => ?_
      rw [← hfP] at hw'
      exact (hPo.frontier_eq ▸ hw').2 hw
    -- `P` avoids the curve
    have hPC : Disjoint P C := by
      refine Set.disjoint_left.2 fun x hxP hxC => ?_
      by_cases hxg : x ∈ g '' Icc 0 1
      · exact (Set.disjoint_left.1 hPJ) hxP (Or.inr hxg)
      · obtain ⟨S, hSc, hxS, hSsub, hSu⟩ := hrest x ⟨hxC, hxg⟩
        have hSk : Disjoint S (k '' Icc 0 1) := by
          refine Set.disjoint_left.2 fun w hw hw' => ?_
          rw [image_Icc_eq_union_endpoints, hk0, hk1] at hw'
          rcases hw' with h | h
          · exact (Set.disjoint_left.1 hDC) (hkD h) (hSsub hw).1
          · rcases h with rfl | rfl
            · exact (hSsub hw).2 ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
            · exact (hSsub hw).2 ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
        have hScover : S ⊆ P ∪ Q := by
          rw [hPQu]
          intro w hw hw'
          rcases hw' with h | h
          · exact (Set.disjoint_left.1 hSk) hw h
          · exact (hSsub hw).2 h
        have hSP : S ⊆ P :=
          hSc.subset_left_of_subset_union hPo hQo hPQd hScover ⟨x, hxS, hxP⟩
        exact hSu (hPb.subset hSP)
    -- `P` lies in `D`
    have hPD : P ⊆ D := by
      have hcover : P ⊆ D ∪ E := by
        intro w hw
        rw [hunion]
        exact fun hc => (Set.disjoint_left.1 hPC) hw hc
      have hne : (P ∩ D).Nonempty := by
        have hy : k (1/2) ∈ k '' Ioo 0 1 := ⟨1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
        have hyD : k (1/2) ∈ D := hkD hy
        have hyfr : k (1/2) ∈ frontier P := by
          rw [hfP]; exact Or.inl (Set.image_mono Ioo_subset_Icc_self hy)
        obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hDo _ hyD
        obtain ⟨w, hwP, hwd⟩ := Metric.mem_closure_iff.1 hyfr.1 r hr
        exact ⟨w, hwP, hrsub (by rwa [mem_ball, dist_comm])⟩
      exact hPc.isPreconnected.subset_left_of_subset_union hDo hEo hdisjDE hcover hne
    exact ⟨P, hPo, hPc, hPD, hPb, hfP⟩
  rcases hbdd with ⟨hb, hu⟩ | ⟨hb, hu⟩
  · exact main P Q hPo hQo hPc hPQd hPQu hfP hb hu
  · exact main Q P hQo hPo hQc hPQd.symm (by rw [union_comm]; exact hPQu) hfQ hb hu

/-- **The local part of Theorem 4** of Klein–Langetepe–Nilforoushan (2009) for the
*unbounded* Jordan curves of axiom `A₁`, derived from the local connectedness of the two
complementary domains at the points of the curve:

> For each point `z ∈ C` there exists a neighbourhood `U` whose boundary is homeomorphic to
> a circle, such that `U \ C` consists of exactly two connected components.  Point `z` is
> accessible from each domain `U ∩ Dᵢ`.

The data required by `AVD.exists_local_nbhd_of_data` are assembled from a proper line
parametrization `Γ` of `C` (`AVD.IsUnboundedJordanCurve.exists_properParam`): a short
parameter interval around `z` cuts out a small arc `g₁`, whose endpoints are joined inside
each `Dᵢ` by a small crosscut `kᵢ` (`AVD.exists_crosscut_near`), and the small domains `Ωᵢ`
are the bounded complementary domains of the closed Jordan curves `kᵢ ∪ g₁`
(`AVD.exists_bounded_crosscut_domain`, applicable because the two ends of `C` are
unbounded). -/
theorem IsUnboundedJordanCurve.exists_local_nbhd {C D₁ D₂ : Set Plane}
    (hC : IsUnboundedJordanCurve C) (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (hdisj : Disjoint D₁ D₂) (hunion : D₁ ∪ D₂ = Cᶜ)
    (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    (hlc1 : ∀ y ∈ C, LocallyConnectedAt D₁ y) (hlc2 : ∀ y ∈ C, LocallyConnectedAt D₂ y)
    {z : Plane} (hz : z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set Plane, IsOpen U ∧ z ∈ U ∧ U ⊆ ball z ε ∧
      IsClosedJordanCurve (frontier U) ∧
      IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
      (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
      (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z) := by
  classical
  obtain ⟨Γ, hcont, hinj, hrange, hproper⟩ := hC.exists_properParam
  have hclosedmap : IsClosedMap Γ :=
    (isProperMap_iff_isCompact_preimage.2 ⟨hcont, hproper⟩).isClosedMap
  obtain ⟨u₀, hu₀⟩ : ∃ u, Γ u = z := by rw [← hrange] at hz; exact hz
  -- the images of unbounded parameter sets are unbounded
  have hunb : ∀ T : Set ℝ, ¬ Bornology.IsBounded T → ¬ Bornology.IsBounded (Γ '' T) := by
    intro T hT hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : Plane)
    have hcomp : IsCompact (Γ ⁻¹' closedBall (0 : Plane) R) :=
      hproper _ (isCompact_closedBall 0 R)
    exact hT (hcomp.isBounded.subset fun r hr => hR ⟨r, hr, rfl⟩)
  set ε₁ : ℝ := ε / 2 with hε₁def
  have hε₁ : 0 < ε₁ := by simp only [hε₁def]; linarith
  have hε₁ε : ε₁ < ε := by simp only [hε₁def]; linarith
  obtain ⟨δ₁, hδ₁, hcross₁⟩ := exists_crosscut_near h1o hf1 hlc1 hz hε₁
  obtain ⟨δ₂, hδ₂, hcross₂⟩ := exists_crosscut_near h2o hf2 hlc2 hz hε₁
  set δ : ℝ := min (min δ₁ δ₂) ε₁ with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) hε₁
  -- a short parameter interval around `u₀`
  obtain ⟨η, hη, hηsub⟩ : ∃ η : ℝ, 0 < η ∧ Γ '' Icc (u₀ - η) (u₀ + η) ⊆ ball z δ := by
    have hopen : IsOpen (Γ ⁻¹' ball z δ) := isOpen_ball.preimage hcont
    have humem : u₀ ∈ Γ ⁻¹' ball z δ := by simp [hu₀, mem_ball_self hδ]
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hopen u₀ humem
    refine ⟨r / 2, by linarith, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    refine hrsub ?_
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hw.1]; linarith [hw.2]]
  set s : ℝ := u₀ - η with hs
  set t : ℝ := u₀ + η with ht
  have hst : s < t := by simp only [hs, ht]; linarith
  set a : Plane := Γ s with hadef
  set b : Plane := Γ t with hbdef
  -- the small arc of the curve around `z`
  set g₁ : ℝ → Plane := fun x => Γ (s + (t - s) * x) with hg₁def
  have hmem : ∀ x ∈ Icc (0 : ℝ) 1, s + (t - s) * x ∈ Icc s t := by
    intro x hx; constructor <;> nlinarith [hx.1, hx.2]
  have hnezero : t - s ≠ 0 := by simp only [hs, ht]; intro hcon; linarith
  have harc₁ : IsArc g₁ := by
    refine ⟨(hcont.comp (by fun_prop)).continuousOn, ?_⟩
    intro x _ y _ hxy
    have h := hinj hxy
    exact mul_left_cancel₀ hnezero (by linarith)
  have h₁₀ : g₁ 0 = a := by simp [hg₁def, hadef]
  have h₁₁ : g₁ 1 = b := by simp [hg₁def, hbdef]
  have himg : g₁ '' Icc 0 1 = Γ '' Icc s t := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩; exact ⟨_, hmem x hx, rfl⟩
    · rintro y ⟨w, hw, rfl⟩
      refine ⟨(w - s) / (t - s), ⟨div_nonneg (by linarith [hw.1]) (by linarith),
        by rw [div_le_one (by linarith)]; linarith [hw.2]⟩, ?_⟩
      change Γ (s + (t - s) * ((w - s) / (t - s))) = Γ w
      rw [show (t - s) * ((w - s) / (t - s)) = w - s by field_simp]
      congr 1; ring
  have himgIoo : g₁ '' Ioo 0 1 = Γ '' Ioo s t := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨_, ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩, rfl⟩
    · rintro y ⟨w, hw, rfl⟩
      refine ⟨(w - s) / (t - s), ⟨div_pos (by linarith [hw.1]) (by linarith),
        by rw [div_lt_one (by linarith)]; linarith [hw.2]⟩, ?_⟩
      change Γ (s + (t - s) * ((w - s) / (t - s))) = Γ w
      rw [show (t - s) * ((w - s) / (t - s)) = w - s by field_simp]
      congr 1; ring
  have hA₁C : g₁ '' Icc 0 1 ⊆ C := by
    rw [himg]
    rintro y ⟨w, -, rfl⟩
    rw [← hrange]; exact mem_range_self w
  -- the complement of the small arc in the curve
  set A₂ : Set Plane := Γ '' (Iic s ∪ Ici t) with hA₂def
  have hA₂closed : IsClosed A₂ := hclosedmap _ (isClosed_Iic.union isClosed_Ici)
  have hcovR : Icc s t ∪ (Iic s ∪ Ici t) = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Icc, mem_Iic, mem_Ici, mem_univ, iff_true]
    rcases le_or_gt x s with h | h
    · exact Or.inr (Or.inl h)
    · rcases le_or_gt t x with h' | h'
      · exact Or.inr (Or.inr h')
      · exact Or.inl ⟨le_of_lt h, le_of_lt h'⟩
  have hCeq : g₁ '' Icc 0 1 ∪ A₂ = C := by
    rw [himg, hA₂def, ← Set.image_union, hcovR, Set.image_univ, hrange]
  have hI₁A₂ : Disjoint (g₁ '' Ioo 0 1) A₂ := by
    rw [himgIoo, hA₂def]
    refine Set.disjoint_left.2 ?_
    rintro y ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
    have := hinj hww'
    subst this
    rcases hw' with h | h
    · exact absurd h (not_le.2 hw.1)
    · exact absurd h (not_le.2 hw.2)
  have habA₂ : a ∈ A₂ ∧ b ∈ A₂ :=
    ⟨⟨s, Or.inl (le_refl s), rfl⟩, ⟨t, Or.inr (le_refl t), rfl⟩⟩
  have hA₁ball : g₁ '' Icc 0 1 ⊆ ball z δ := by
    rw [himg]
    rintro y ⟨w, hw, rfl⟩
    exact hηsub ⟨w, hw, rfl⟩
  have hzI₁ : z ∈ g₁ '' Ioo 0 1 := by
    rw [himgIoo]
    exact ⟨u₀, ⟨by simp only [hs]; linarith, by simp only [ht]; linarith⟩, hu₀⟩
  have haC : a ∈ C := by rw [hadef, ← hrange]; exact mem_range_self s
  have hbC : b ∈ C := by rw [hbdef, ← hrange]; exact mem_range_self t
  have hab : a ≠ b := by
    intro hcon
    have := hinj hcon
    simp only [hs, ht] at this
    linarith
  have haball : a ∈ ball z δ := hηsub ⟨s, ⟨le_refl _, by simp only [hs, ht]; linarith⟩, rfl⟩
  have hbball : b ∈ ball z δ := hηsub ⟨t, ⟨by simp only [hs, ht]; linarith, le_refl _⟩, rfl⟩
  have hda : dist a z < δ := by rwa [mem_ball] at haball
  have hdb : dist b z < δ := by rwa [mem_ball] at hbball
  -- the two crosscuts
  obtain ⟨k₁, hk₁, hk₁₀, hk₁₁, hk₁sub⟩ := hcross₁ a haC b hbC
    (lt_of_lt_of_le hda (le_trans (min_le_left _ _) (min_le_left _ _)))
    (lt_of_lt_of_le hdb (le_trans (min_le_left _ _) (min_le_left _ _))) hab
  obtain ⟨k₂, hk₂, hk₂₀, hk₂₁, hk₂sub⟩ := hcross₂ a haC b hbC
    (lt_of_lt_of_le hda (le_trans (min_le_left _ _) (min_le_right _ _)))
    (lt_of_lt_of_le hdb (le_trans (min_le_left _ _) (min_le_right _ _))) hab
  -- every point of the curve outside the small arc lies on an unbounded end
  have hrest : ∀ x ∈ C \ g₁ '' Icc 0 1, ∃ S : Set Plane, IsPreconnected S ∧ x ∈ S ∧
      S ⊆ C \ g₁ '' Icc 0 1 ∧ ¬ Bornology.IsBounded S := by
    rintro x ⟨hxC, hxg⟩
    rw [← hrange] at hxC
    obtain ⟨r, rfl⟩ := hxC
    have hr : r < s ∨ t < r := by
      by_contra hcon
      push Not at hcon
      exact hxg (by rw [himg]; exact ⟨r, ⟨hcon.1, hcon.2⟩, rfl⟩)
    have hsubC : ∀ T : Set ℝ, (∀ r' ∈ T, r' < s ∨ t < r') →
        Γ '' T ⊆ C \ g₁ '' Icc 0 1 := by
      intro T hT y hy
      obtain ⟨r', hr', rfl⟩ := hy
      refine ⟨by rw [← hrange]; exact mem_range_self r', ?_⟩
      rw [himg]
      rintro ⟨w, hw, hwr⟩
      have heq : w = r' := hinj hwr
      rw [heq] at hw
      rcases hT r' hr' with h | h
      · linarith [hw.1]
      · linarith [hw.2]
    rcases hr with h | h
    · refine ⟨Γ '' Iio s, isPreconnected_Iio.image Γ hcont.continuousOn, ⟨r, h, rfl⟩,
        hsubC _ (fun r' hr' => Or.inl hr'), hunb _ ?_⟩
      intro hbd
      obtain ⟨R, hR⟩ := hbd.subset_closedBall (0 : ℝ)
      have hmem' : min (-R - 1) (s - 1) ∈ Iio s :=
        lt_of_le_of_lt (min_le_right (-R - 1) (s - 1)) (by linarith)
      have h1 := hR hmem'
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at h1
      linarith [h1.1, min_le_left (-R - 1) (s - 1)]
    · refine ⟨Γ '' Ioi t, isPreconnected_Ioi.image Γ hcont.continuousOn, ⟨r, h, rfl⟩,
        hsubC _ (fun r' hr' => Or.inr hr'), hunb _ ?_⟩
      intro hbd
      obtain ⟨R, hR⟩ := hbd.subset_closedBall (0 : ℝ)
      have hmem' : max (R + 1) (t + 1) ∈ Ioi t :=
        lt_of_lt_of_le (show t < t + 1 by linarith) (le_max_right (R + 1) (t + 1))
      have h1 := hR hmem'
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le] at h1
      linarith [h1.2, le_max_left (R + 1) (t + 1)]
  -- the two small domains
  obtain ⟨Ω₁, hΩ₁o, hΩ₁c, hΩ₁D, hΩ₁b, hfΩ₁⟩ :=
    exists_bounded_crosscut_domain h1o h2o hdisj hunion harc₁ hk₁ (hk₁₀.trans h₁₀.symm)
      (hk₁₁.trans h₁₁.symm) (fun w hw => (hk₁sub hw).1) hA₁C hrest
  obtain ⟨Ω₂, hΩ₂o, hΩ₂c, hΩ₂D, hΩ₂b, hfΩ₂⟩ :=
    exists_bounded_crosscut_domain h2o h1o hdisj.symm (by rw [union_comm]; exact hunion)
      harc₁ hk₂ (hk₂₀.trans h₁₀.symm) (hk₂₁.trans h₁₁.symm) (fun w hw => (hk₂sub hw).1)
      hA₁C hrest
  -- the two small domains are small
  have hKball : ∀ (k : ℝ → Plane), k 0 = a → k 1 = b → k '' Ioo 0 1 ⊆ ball z ε₁ →
      k '' Icc 0 1 ⊆ closedBall z ε₁ := by
    intro k hk0 hk1 hksub
    rw [image_Icc_eq_union_endpoints, hk0, hk1]
    rintro w (hw | hw)
    · exact ball_subset_closedBall (hksub hw)
    · rcases hw with rfl | rfl
      · exact ball_subset_closedBall (ball_subset_ball (min_le_right _ _) haball)
      · exact ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hbball)
  have hsmall : ∀ Ω : Set Plane, IsOpen Ω → Bornology.IsBounded Ω →
      frontier Ω ⊆ closedBall z ε₁ → Ω ⊆ closedBall z ε₁ := by
    intro Ω hΩo hΩb hfr
    obtain ⟨R, hR⟩ := hΩb.subset_closedBall z
    obtain ⟨y, hy⟩ := exists_dist_gt z (max R ε₁)
    refine subset_closedBall_of_frontier_subset hΩo hε₁ hfr (y := y) ?_ ?_
    · simp only [mem_closedBall, not_le]
      exact lt_of_le_of_lt (le_max_right R ε₁) hy
    · intro hcon
      have := hR hcon
      rw [mem_closedBall] at this
      exact absurd (lt_of_le_of_lt (le_max_left R ε₁) hy) (not_lt.2 this)
  have hA₁ball' : g₁ '' Icc 0 1 ⊆ ball z ε₁ :=
    fun w hw => ball_subset_ball (min_le_right _ _) (hA₁ball hw)
  have hΩ₁small : Ω₁ ⊆ closedBall z ε₁ := by
    refine hsmall Ω₁ hΩ₁o hΩ₁b ?_
    rw [hfΩ₁]
    exact union_subset (hKball k₁ hk₁₀ hk₁₁ (fun w hw => (hk₁sub hw).2))
      (fun w hw => ball_subset_closedBall (hA₁ball' hw))
  have hΩ₂small : Ω₂ ⊆ closedBall z ε₁ := by
    refine hsmall Ω₂ hΩ₂o hΩ₂b ?_
    rw [hfΩ₂]
    exact union_subset (hKball k₂ hk₂₀ hk₂₁ (fun w hw => (hk₂sub hw).2))
      (fun w hw => ball_subset_closedBall (hA₁ball' hw))
  obtain ⟨U, hUopen, hzU, hUsmall, hJ, hc1, hc2, hacc1, hacc2⟩ :=
    exists_local_nbhd_of_data (C := C) (A₂ := A₂) (a := a) (b := b) (ε₁ := ε₁)
      h1o h2o hdisj hunion hf1 hf2 hlc1 hlc2 hz harc₁ hk₁ hk₂
      h₁₀ h₁₁ hk₁₀ hk₁₁ hk₂₀ hk₂₁ hk₁sub hk₂sub hA₂closed hCeq hI₁A₂ habA₂
      hA₁ball' hzI₁ hΩ₁o hΩ₁c hΩ₁D hfΩ₁ hΩ₁small hΩ₂o hΩ₂c hΩ₂D hfΩ₂ hΩ₂small
  exact ⟨U, hUopen, hzU, fun w hw => closedBall_subset_ball hε₁ε (hUsmall hw), hJ, hc1, hc2,
    hacc1, hacc2⟩

end AVD
