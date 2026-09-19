import AbstractVoronoi.Jordan.PlaneTools

/-!
# The θ-curve theorem for a circular crosscut

The classical θ-curve theorem says that a crosscut `κ` of a complementary domain `D` of a
closed Jordan curve splits `D ∖ κ` into exactly the two Jordan domains `Ω₁, Ω₂` bounded by
`κ` and by the two arcs of the curve (the constructive half of that statement is
`AVD.exists_crosscut_domains`).  Classically it is deduced from Janiszewski's theorem, and in
`AbstractVoronoi.Jordan.ThetaCurve` it is deduced from the local connectedness of `D` at the points
of the curve.

Here it is proved **with no extra hypothesis at all** for the crosscuts that lie on a
*circle* — which is exactly the kind of crosscut produced by
`AVD.exists_circular_crosscut`.  The reason is that a circle is *locally two-sided*: at a
point `q` of the circle, small balls around `q` meet the complement of the circle in two
connected pieces only, the inner piece `ball q b ∩ ball z r` and its image under the radial
reflection `w ↦ z + ((2r - ‖w - z‖)/‖w - z‖) • (w - z)` in the circle.  A third connected
component of `D ∖ κ` would have a frontier point `q` in the relative interior of `κ`, and so
do the two domains `Ω₁, Ω₂`; the three components would then have to share the two pieces,
which is impossible.

This is the tool for the local part of **Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-! ## The radial reflection in a circle -/

/-- The **radial reflection** in the circle of centre `z` and radius `r`: the point `w` is
moved along the ray from `z` through `w` to the point at distance `2r - ‖w - z‖` from `z`.
It fixes the circle pointwise and exchanges the punctured open disc with the open annulus
`r < ‖w - z‖ < 2r`; it is used to produce, out of the inner half of a small ball centred at a
point of the circle, a connected piece covering the outer half. -/
def radialRefl (z : Plane) (r : ℝ) (w : Plane) : Plane :=
  z + ((2 * r - ‖w - z‖) / ‖w - z‖) • (w - z)

/-- The radial reflection, written as a dilation of the vector `w - z`. -/
theorem radialRefl_sub (z : Plane) (r : ℝ) (w : Plane) :
    radialRefl z r w - z = ((2 * r - ‖w - z‖) / ‖w - z‖) • (w - z) := by
  simp [radialRefl]

/-- The radial reflection moves `w` to distance `|2r - ‖w - z‖|` from the centre `z`. -/
theorem norm_radialRefl_sub {z w : Plane} (r : ℝ) (hw : w ≠ z) :
    ‖radialRefl z r w - z‖ = |2 * r - ‖w - z‖| := by
  have hs : 0 < ‖w - z‖ := by
    rw [norm_pos_iff, sub_ne_zero]; exact hw
  rw [radialRefl_sub, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hs,
    div_mul_cancel₀ _ (ne_of_gt hs)]

/-- The radial reflection in a circle fixes that circle pointwise. -/
theorem radialRefl_eq_self {z q : Plane} {r : ℝ} (hr : 0 < r) (hq : q ∈ sphere z r) :
    radialRefl z r q = q := by
  have hs : ‖q - z‖ = r := by
    rw [mem_sphere, dist_eq_norm] at hq; exact hq
  rw [radialRefl, hs]
  have h : (2 * r - r) / r = 1 := by
    rw [show 2 * r - r = r by ring, div_self (ne_of_gt hr)]
  rw [h, one_smul, add_sub_cancel]

/-- The radial reflection is continuous away from the centre. -/
theorem continuousAt_radialRefl (z : Plane) (r : ℝ) {w : Plane} (hw : w ≠ z) :
    ContinuousAt (radialRefl z r) w := by
  have h : ‖w - z‖ ≠ 0 := by
    rw [ne_eq, norm_eq_zero, sub_eq_zero]; exact hw
  have h1 : ContinuousAt (fun w : Plane => w - z) w :=
    (continuous_id.sub continuous_const).continuousAt
  have h2 : ContinuousAt (fun w : Plane => ‖w - z‖) w := h1.norm
  have h3 : ContinuousAt (fun w : Plane => (2 * r - ‖w - z‖) / ‖w - z‖) w :=
    (continuousAt_const.sub h2).div h2 h
  exact continuousAt_const.add (h3.smul h1)

/-- The radial reflection is an involution on the punctured open disc of radius `2r`. -/
theorem radialRefl_radialRefl {z w : Plane} {r : ℝ} (hw : w ≠ z)
    (hlt : ‖w - z‖ < 2 * r) : radialRefl z r (radialRefl z r w) = w := by
  have hspos : 0 < ‖w - z‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hw
  have hnorm : ‖radialRefl z r w - z‖ = 2 * r - ‖w - z‖ := by
    rw [norm_radialRefl_sub r hw, abs_of_pos (by linarith)]
  rw [radialRefl, hnorm, radialRefl_sub, smul_smul]
  have h : (2 * r - (2 * r - ‖w - z‖)) / (2 * r - ‖w - z‖) *
      ((2 * r - ‖w - z‖) / ‖w - z‖) = 1 := by
    have h1 : (2 : ℝ) * r - ‖w - z‖ ≠ 0 := by linarith
    field_simp
    ring
  rw [h, one_smul, add_sub_cancel]

/-! ## Local two-sidedness of a circle -/

/-- **A circle is locally two-sided.**  Let `q` be a point of the circle of centre `z` and
radius `r`, and let `ρ > 0`.  Then there is `ρ' > 0` such that the points of `ball q ρ'` off
the circle are covered by two connected sets `N₁, N₂ ⊆ ball q ρ`, both disjoint from the
circle: the inner piece `ball q b ∩ ball z r` and its image under the radial reflection
`AVD.radialRefl`. -/
theorem exists_two_sided_nbhd (z : Plane) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) {q : Plane}
    (hq : q ∈ sphere z r) :
    ∃ ρ' > 0, ρ' ≤ ρ ∧ ∃ N₁ N₂ : Set Plane,
      IsPreconnected N₁ ∧ IsPreconnected N₂ ∧ N₁ ⊆ ball q ρ ∧ N₂ ⊆ ball q ρ ∧
      Disjoint N₁ (sphere z r) ∧ Disjoint N₂ (sphere z r) ∧
      ball q ρ' \ sphere z r ⊆ N₁ ∪ N₂ := by
  have hqz : ‖q - z‖ = r := by rw [mem_sphere, dist_eq_norm] at hq; exact hq
  have hqne : q ≠ z := by
    intro h
    rw [h, sub_self, norm_zero] at hqz
    exact absurd hqz.symm (ne_of_gt hr)
  -- points of `ball q c` with `c ≤ r / 2` are at distance between `r/2` and `3r/2` from `z`
  have hdist : ∀ c : ℝ, c ≤ r / 2 → ∀ w ∈ ball q c, r / 2 < ‖w - z‖ ∧ ‖w - z‖ < 3 * r / 2 := by
    intro c hc w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 : ‖w - z‖ ≤ ‖w - q‖ + ‖q - z‖ := norm_sub_le_norm_sub_add_norm_sub w q z
    have h2 : ‖q - z‖ ≤ ‖q - w‖ + ‖w - z‖ := norm_sub_le_norm_sub_add_norm_sub q w z
    rw [norm_sub_rev q w] at h2
    rw [hqz] at h1 h2
    constructor <;> linarith
  have hfix : radialRefl z r q = q := radialRefl_eq_self hr hq
  have hcont : ContinuousAt (radialRefl z r) q := continuousAt_radialRefl z r hqne
  -- `b`: the reflection of `ball q b` stays in `ball q ρ`
  obtain ⟨b₀, hb₀pos, hb₀⟩ := Metric.continuousAt_iff.1 hcont ρ hρ
  set b : ℝ := min b₀ (min ρ (r / 2)) with hbdef
  have hbpos : 0 < b := lt_min hb₀pos (lt_min hρ (by linarith))
  have hbb₀ : b ≤ b₀ := min_le_left _ _
  have hbρ : b ≤ ρ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hbr : b ≤ r / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- `ρ'`: the reflection of `ball q ρ'` stays in `ball q b`
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Metric.continuousAt_iff.1 hcont b hbpos
  refine ⟨min c₀ b, lt_min hc₀pos hbpos, le_trans (min_le_right _ _) hbρ, ball q b ∩ ball z r,
    radialRefl z r '' (ball q b ∩ ball z r), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((convex_ball q b).inter (convex_ball z r)).isPreconnected
  · refine (((convex_ball q b).inter (convex_ball z r)).isPreconnected).image _ ?_
    intro w hw
    have hwz : w ≠ z := by
      intro h
      have := (hdist b hbr w hw.1).1
      rw [h, sub_self, norm_zero] at this
      linarith
    exact (continuousAt_radialRefl z r hwz).continuousWithinAt
  · exact fun w hw => ball_subset_ball hbρ hw.1
  · rintro _ ⟨w, hw, rfl⟩
    have hd : dist w q < b₀ := lt_of_lt_of_le (mem_ball.1 hw.1) hbb₀
    have hres := hb₀ hd
    rw [hfix] at hres
    exact mem_ball.2 hres
  · refine Set.disjoint_left.2 fun w hw hws => ?_
    have hwr : ‖w - z‖ < r := by rw [← dist_eq_norm]; exact mem_ball.1 hw.2
    rw [mem_sphere, dist_eq_norm] at hws
    rw [hws] at hwr
    exact lt_irrefl r hwr
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ hws
    have hwz : w ≠ z := by
      intro h
      have := (hdist b hbr w hw.1).1
      rw [h, sub_self, norm_zero] at this
      linarith
    have hlt : ‖w - z‖ < r := by
      have := hw.2
      rwa [mem_ball, dist_eq_norm] at this
    rw [mem_sphere, dist_eq_norm, norm_radialRefl_sub r hwz, abs_of_pos (by linarith)] at hws
    linarith
  · rintro w ⟨hw, hws⟩
    have hwb : w ∈ ball q b := ball_subset_ball (min_le_right _ _) hw
    obtain ⟨hlow, hhigh⟩ := hdist b hbr w hwb
    have hwz : w ≠ z := by
      intro h
      rw [h, sub_self, norm_zero] at hlow
      linarith
    have hne : ‖w - z‖ ≠ r := by
      intro h
      exact hws (by rw [mem_sphere, dist_eq_norm, h])
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hwb, by rw [mem_ball, dist_eq_norm]; exact hlt⟩
    · refine Or.inr ⟨radialRefl z r w, ⟨?_, ?_⟩, ?_⟩
      · have hd : dist w q < c₀ := lt_of_lt_of_le (mem_ball.1 hw) (min_le_left _ _)
        have hres := hc₀ hd
        rw [hfix] at hres
        exact hres
      · rw [mem_ball, dist_eq_norm, norm_radialRefl_sub r hwz, abs_of_pos (by linarith)]
        linarith
      · exact radialRefl_radialRefl hwz (by linarith)

/-! ## The θ-curve theorem for a circular crosscut -/

/-- **The θ-curve theorem for a crosscut lying on a circle**, with no extra hypothesis.

Let `D` be an open connected set, let `K` be a closed subset of the circle of centre `z` and
radius `r` which meets `D` and is relatively open in the circle at each of its points lying
in `D` (in the application `K` is the image of a crosscut of `D` obtained from
`AVD.exists_circular_crosscut`, and `K ∩ D` is its relative interior, a connected component
of `D` intersected with the circle, which is open in the circle).  Let `Ω₁, Ω₂` be two
disjoint non-empty open connected subsets of `D`, each of which has `K` on its frontier and
meets `D` in its frontier only along `K` (in the application, the two domains cut off by the
crosscut, as produced by `AVD.exists_crosscut_domains`).  Then `Ω₁` and `Ω₂` exhaust `D ∖ K`.

Indeed `Ω₁` and `Ω₂` are then connected components of `D ∖ K`, and a third component `V`
would, `D` being connected, have a frontier point `q` in `K ∩ D`; small balls around `q` meet
`D ∖ K` in two connected pieces only (`AVD.exists_two_sided_nbhd`), while all three of `V`,
`Ω₁`, `Ω₂` have points there. -/
theorem circular_crosscut_exhausts {D : Set Plane} (hDo : IsOpen D) (hDconn : IsPreconnected D)
    {z : Plane} {r : ℝ} (hr : 0 < r)
    {K : Set Plane} (hKclosed : IsClosed K) (hKsph : K ⊆ sphere z r)
    (hKrel : ∀ q ∈ K ∩ D, ∃ ρ > 0, ball q ρ ∩ sphere z r ⊆ K)
    (hKDne : (K ∩ D).Nonempty)
    {Ω₁ Ω₂ : Set Plane} (hΩ₁o : IsOpen Ω₁) (hΩ₂o : IsOpen Ω₂)
    (hΩ₁c : IsPreconnected Ω₁) (hΩ₂c : IsPreconnected Ω₂)
    (hΩ₁D : Ω₁ ⊆ D) (hΩ₂D : Ω₂ ⊆ D) (hdisj : Disjoint Ω₁ Ω₂)
    (hKfr₁ : K ⊆ frontier Ω₁) (hKfr₂ : K ⊆ frontier Ω₂)
    (hfr₁D : frontier Ω₁ ∩ D ⊆ K) (hfr₂D : frontier Ω₂ ∩ D ⊆ K) :
    D \ K ⊆ Ω₁ ∪ Ω₂ := by
  set U : Set Plane := D \ K with hUdef
  have hUopen : IsOpen U := hDo.sdiff hKclosed
  -- an open set is disjoint from its frontier
  have hopen_fr : ∀ S : Set Plane, IsOpen S → Disjoint S (frontier S) := fun S hS =>
    Set.disjoint_left.2 fun w hw hw' => (hS.frontier_eq ▸ hw').2 hw
  have hΩU : ∀ Ω : Set Plane, IsOpen Ω → Ω ⊆ D → K ⊆ frontier Ω → Ω ⊆ U := by
    intro Ω hΩ hΩD hKfr w hw
    exact ⟨hΩD hw, fun hwK => (Set.disjoint_left.1 (hopen_fr Ω hΩ)) hw (hKfr hwK)⟩
  have hΩ₁U : Ω₁ ⊆ U := hΩU Ω₁ hΩ₁o hΩ₁D hKfr₁
  have hΩ₂U : Ω₂ ⊆ U := hΩU Ω₂ hΩ₂o hΩ₂D hKfr₂
  -- each `Ωᵢ` is a whole connected component of `U`
  have hcomp : ∀ Ω : Set Plane, IsOpen Ω → IsPreconnected Ω → Ω ⊆ U →
      frontier Ω ∩ D ⊆ K → ∀ w ∈ Ω, connectedComponentIn U w = Ω := by
    intro Ω hΩ hΩc hΩU hfrΩ w hw
    have hsub : Ω ⊆ connectedComponentIn U w := hΩc.subset_connectedComponentIn hw hΩU
    refine subset_antisymm ?_ hsub
    by_contra hcon
    obtain ⟨y, hyC, hyΩ⟩ := not_subset.1 hcon
    -- `Ω` is open, non-empty and not all of the component, so the component meets its frontier
    have hPconn : IsPreconnected (connectedComponentIn U w) := isPreconnected_connectedComponentIn
    have hcover : ¬ (connectedComponentIn U w ⊆ Ω ∪ (closure Ω)ᶜ) := by
      intro hc
      have hdis : Disjoint Ω ((closure Ω)ᶜ) :=
        Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
      have := hPconn.subset_left_of_subset_union hΩ isClosed_closure.isOpen_compl hdis hc
        ⟨w, mem_connectedComponentIn (hΩU hw), hw⟩
      exact hyΩ (this hyC)
    obtain ⟨p, hpC, hpn⟩ := not_subset.1 hcover
    have hpΩ : p ∉ Ω := fun h => hpn (Or.inl h)
    have hpcl : p ∈ closure Ω := by
      by_contra h
      exact hpn (Or.inr h)
    have hpfr : p ∈ frontier Ω := ⟨hpcl, by rwa [hΩ.interior_eq]⟩
    have hpD : p ∈ D := (connectedComponentIn_subset U w hpC).1
    exact (connectedComponentIn_subset U w hpC).2 (hfrΩ ⟨hpfr, hpD⟩)
  intro x hx
  by_contra hxA
  have hx₁ : x ∉ Ω₁ := fun h => hxA (Or.inl h)
  have hx₂ : x ∉ Ω₂ := fun h => hxA (Or.inr h)
  set V : Set Plane := connectedComponentIn U x with hVdef
  have hxV : x ∈ V := mem_connectedComponentIn hx
  have hVU : V ⊆ U := connectedComponentIn_subset U x
  have hVopen : IsOpen V := hUopen.connectedComponentIn
  -- the frontier of `V` meets `D`, hence `K ∩ D`
  have hfrVD : frontier V ∩ D ⊆ K ∩ D := by
    rintro w ⟨hwfr, hwD⟩
    refine ⟨?_, hwD⟩
    have h : U = D ∩ Kᶜ := by rw [hUdef, Set.sdiff_eq]
    have hfrU : frontier U ⊆ frontier D ∪ K := by
      rw [h]
      refine (frontier_inter_subset D Kᶜ).trans ?_
      rintro y (hy | hy)
      · exact Or.inl hy.1
      · refine Or.inr ?_
        have h2 := hy.2
        rw [frontier_compl] at h2
        exact hKclosed.frontier_subset h2
    rcases hfrU (frontier_connectedComponentIn_subset hUopen hwfr) with hy | hy
    · exact absurd hwD (hDo.frontier_eq ▸ hy).2
    · exact hy
  have hfrVne : (frontier V ∩ D).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    -- then `V` is open and closed in `D`, so `V = D`, contradicting `K ∩ D ≠ ∅`
    have hcover : D ⊆ V ∪ (closure V)ᶜ := by
      intro w hw
      by_cases h : w ∈ closure V
      · refine Or.inl ?_
        by_contra hv
        have hmemfr : w ∈ frontier V ∩ D := ⟨⟨h, by rwa [hVopen.interior_eq]⟩, hw⟩
        rw [hcon] at hmemfr
        exact hmemfr.elim
      · exact Or.inr h
    have hdis : Disjoint V ((closure V)ᶜ) :=
      Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
    have hDV : D ⊆ V := hDconn.subset_left_of_subset_union hVopen
      isClosed_closure.isOpen_compl hdis hcover ⟨x, hx.1, hxV⟩
    obtain ⟨y, hyK, hyD⟩ := hKDne
    exact (hVU (hDV hyD)).2 hyK
  obtain ⟨q, hqfr, hqD⟩ := hfrVne
  obtain ⟨hqK, -⟩ := hfrVD ⟨hqfr, hqD⟩
  -- a ball around `q` inside `D` whose intersection with the circle lies in `K`
  obtain ⟨ρ₁, hρ₁, hρ₁K⟩ := hKrel q ⟨hqK, hqD⟩
  obtain ⟨ρ₂, hρ₂, hρ₂D⟩ := Metric.isOpen_iff.1 hDo q hqD
  obtain ⟨ρ', hρ', hρ'le, N₁, N₂, hN₁c, hN₂c, hN₁sub, hN₂sub, hN₁s, hN₂s, hcov⟩ :=
    exists_two_sided_nbhd z hr (lt_min hρ₁ hρ₂) (hKsph hqK)
  -- the two pieces lie in `U`
  have hNU : ∀ N : Set Plane, N ⊆ ball q (min ρ₁ ρ₂) → Disjoint N (sphere z r) → N ⊆ U := by
    intro N hNsub hNs w hw
    refine ⟨hρ₂D (ball_subset_ball (min_le_right _ _) (hNsub hw)), fun hwK => ?_⟩
    exact (Set.disjoint_left.1 hNs) hw (hKsph hwK)
  have hN₁U : N₁ ⊆ U := hNU N₁ hN₁sub hN₁s
  have hN₂U : N₂ ⊆ U := hNU N₂ hN₂sub hN₂s
  -- points of the same piece lie in the same component of `U`
  have hsame : ∀ N : Set Plane, IsPreconnected N → N ⊆ U → ∀ a ∈ N, ∀ b ∈ N,
      connectedComponentIn U a = connectedComponentIn U b := by
    intro N hNc hNU a ha b hb
    have h1 : N ⊆ connectedComponentIn U a := hNc.subset_connectedComponentIn ha hNU
    exact connectedComponentIn_eq (h1 hb)
  -- the three components have points in `ball q ρ'`
  have hballU : ball q ρ' ∩ U ⊆ N₁ ∪ N₂ := by
    rintro w ⟨hw, hwU⟩
    refine hcov ⟨hw, fun hws => hwU.2 (hρ₁K
      ⟨ball_subset_ball (le_trans hρ'le (min_le_left _ _)) hw, hws⟩)⟩
  have hmem : ∀ S : Set Plane, S ⊆ U → q ∈ closure S → ∃ p ∈ S, p ∈ N₁ ∪ N₂ := by
    intro S hSU hqS
    obtain ⟨p, hpS, hpd⟩ := Metric.mem_closure_iff.1 hqS ρ' hρ'
    exact ⟨p, hpS, hballU ⟨by rwa [mem_ball, dist_comm], hSU hpS⟩⟩
  obtain ⟨p₀, hp₀V, hp₀N⟩ := hmem V hVU hqfr.1
  obtain ⟨p₁, hp₁Ω, hp₁N⟩ := hmem Ω₁ hΩ₁U (frontier_subset_closure (hKfr₁ hqK))
  obtain ⟨p₂, hp₂Ω, hp₂N⟩ := hmem Ω₂ hΩ₂U (frontier_subset_closure (hKfr₂ hqK))
  -- the components of the three points are pairwise distinct
  have hc₀ : connectedComponentIn U p₀ = V :=
    (connectedComponentIn_eq (show p₀ ∈ connectedComponentIn U x from hp₀V)).symm
  have hc₁ : connectedComponentIn U p₁ = Ω₁ := hcomp Ω₁ hΩ₁o hΩ₁c hΩ₁U hfr₁D p₁ hp₁Ω
  have hc₂ : connectedComponentIn U p₂ = Ω₂ := hcomp Ω₂ hΩ₂o hΩ₂c hΩ₂U hfr₂D p₂ hp₂Ω
  have h01 : connectedComponentIn U p₀ ≠ connectedComponentIn U p₁ := by
    rw [hc₀, hc₁]; intro h; exact hx₁ (h ▸ hxV)
  have h02 : connectedComponentIn U p₀ ≠ connectedComponentIn U p₂ := by
    rw [hc₀, hc₂]; intro h; exact hx₂ (h ▸ hxV)
  have h12 : connectedComponentIn U p₁ ≠ connectedComponentIn U p₂ := by
    rw [hc₁, hc₂]; intro h
    exact (Set.disjoint_left.1 hdisj) hp₁Ω (h ▸ hp₁Ω)
  -- but two of them lie in the same piece
  rcases hp₀N with h0 | h0 <;> rcases hp₁N with h1 | h1 <;> rcases hp₂N with h2 | h2
  · exact h01 (hsame N₁ hN₁c hN₁U p₀ h0 p₁ h1)
  · exact h01 (hsame N₁ hN₁c hN₁U p₀ h0 p₁ h1)
  · exact h02 (hsame N₁ hN₁c hN₁U p₀ h0 p₂ h2)
  · exact h12 (hsame N₂ hN₂c hN₂U p₁ h1 p₂ h2)
  · exact h12 (hsame N₁ hN₁c hN₁U p₁ h1 p₂ h2)
  · exact h02 (hsame N₂ hN₂c hN₂U p₀ h0 p₂ h2)
  · exact h01 (hsame N₂ hN₂c hN₂U p₀ h0 p₁ h1)
  · exact h01 (hsame N₂ hN₂c hN₂U p₀ h0 p₁ h1)

end AVD
