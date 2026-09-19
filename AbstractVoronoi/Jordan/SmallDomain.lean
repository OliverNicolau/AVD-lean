import AbstractVoronoi.Jordan.SmallCrosscut
import AbstractVoronoi.Jordan.Crosscut

/-!
# Small Jordan subdomains at a boundary point

This file combines the small crosscuts of `AbstractVoronoi.Jordan.SmallCrosscut` with the crosscut
theorem of `AbstractVoronoi.Jordan.Crosscut` to produce, inside a complementary domain `D` of a
closed Jordan curve `C` and near any prescribed point `z ∈ C`, a *small Jordan subdomain*:
an open connected set `Ω ⊆ D` of diameter at most `2ε`, bounded by a crosscut of `D` of
diameter at most `2ε` and by an arc of `C` of diameter at most `2ε`
(`AVD.IsClosedJordanCurve.exists_small_crosscut_domain`).

This is the geometric content of the local (Jordan–Schönflies) part of **Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

except for one point, which is still missing: that the small domain `Ω` can be chosen with
`z` on its boundary (equivalently, that the crosscut can be chosen so that `z` lies on the
*small* one of the two arcs into which its endpoints cut `C`).

Two auxiliary results proved here are of independent use:

* `AVD.isConnected_compl_closedBall_center` — the complement of a closed ball of the plane is
  connected (the statement of `AbstractVoronoi.Jordan.Adapter` for an arbitrary centre);
* `AVD.subset_closedBall_of_frontier_subset` — an open set whose frontier lies in a closed
  ball, and which omits one point outside that ball, is contained in the ball.  This is the
  elementary substitute for "a bounded domain has the diameter of its boundary".
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-! ## An open set with small frontier is small -/

/-- The complement of a closed ball of the plane, with arbitrary centre, is connected. -/
theorem isConnected_compl_closedBall_center (z : Plane) {r : ℝ} (hr : 0 < r) :
    IsConnected ((closedBall z r)ᶜ) := by
  have h := isConnected_compl_closedBall (r := r) hr
  have himg := h.image (fun y : Plane => y + z) (by fun_prop)
  convert himg using 1
  ext y
  simp only [mem_compl_iff, Metric.mem_closedBall, mem_image, dist_eq_norm, not_le]
  constructor
  · intro hy
    refine ⟨y - z, ?_, by abel⟩
    simpa [dist_eq_norm] using hy
  · rintro ⟨x, hx, rfl⟩
    simpa [dist_eq_norm] using hx

/-- An open set whose frontier is contained in a closed ball, and which does not contain
some point outside that ball, is itself contained in the ball.

This is the elementary replacement for the classical statement that a bounded open set has
the same diameter as its frontier; it is what makes the domain cut off by a small crosscut
small. -/
theorem subset_closedBall_of_frontier_subset {Ω : Set Plane} (hΩ : IsOpen Ω) {z : Plane}
    {r : ℝ} (hr : 0 < r) (hfr : frontier Ω ⊆ closedBall z r) {y : Plane}
    (hy : y ∉ closedBall z r) (hyΩ : y ∉ Ω) : Ω ⊆ closedBall z r := by
  by_contra hcon
  obtain ⟨x, hxΩ, hx⟩ := not_subset.1 hcon
  -- the complement of the ball is connected and misses the frontier of `Ω`
  have hconn : IsConnected ((closedBall z r)ᶜ) := isConnected_compl_closedBall_center z hr
  have hsub : (closedBall z r)ᶜ ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro u hu
    by_cases h : u ∈ Ω
    · exact Or.inl h
    · right
      intro hucl
      exact hu (hfr ⟨hucl, by simpa [hΩ.interior_eq] using h⟩)
  have hdisj : Disjoint Ω ((closure Ω)ᶜ) :=
    Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
  have hleft : (closedBall z r)ᶜ ⊆ Ω :=
    hconn.isPreconnected.subset_left_of_subset_union hΩ (isClosed_closure.isOpen_compl)
      hdisj hsub ⟨x, hx, hxΩ⟩
  exact hyΩ (hleft hy)

/-! ## Cutting a closed Jordan curve at two points of a prescribed parameter interval -/

/-- The decomposition of a closed Jordan curve into two arcs, performed at two points given
by their parameters: if `Γ` is a cyclic parametrization of `C` and `s < t` with `t - s < 1`,
then `Γ s` and `Γ t` cut `C` into the arc `Γ '' [s,t]` and the arc `Γ '' [t,s+1]`.

This is the parametrized form of `AVD.IsClosedJordanCurve.exists_arc_decomposition`; the
extra information it carries — the parameter intervals of the two arcs — is what allows one
to know that one of the two arcs is *small*. -/
theorem exists_arc_decomposition_param {C : Set Plane} {Γ : ℝ → Plane}
    (hΓ : IsCyclicParam Γ C) {s t : ℝ} (hst : s < t) (hlen : t - s < 1) :
    ∃ γ₁ γ₂ : ℝ → Plane, IsArc γ₁ ∧ IsArc γ₂ ∧ γ₁ 0 = Γ s ∧ γ₁ 1 = Γ t ∧
      γ₂ 0 = Γ s ∧ γ₂ 1 = Γ t ∧
      γ₁ '' Icc 0 1 = Γ '' Icc s t ∧
      γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 = C ∧ Disjoint (γ₁ '' Ioo 0 1) (γ₂ '' Ioo 0 1) := by
  have hts1 : t < s + 1 := by linarith
  have key : ∀ c d : ℝ, c < d → d - c < 1 →
      ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = Γ c ∧ γ 1 = Γ d ∧
        γ '' Icc 0 1 = Γ '' Icc c d ∧ γ '' Ioo 0 1 ⊆ Γ '' Ioo c d := by
    intro c d hcd hlen'
    have hmem : ∀ x ∈ Icc (0 : ℝ) 1, c + (d - c) * x ∈ Icc c d := by
      intro x hx; constructor <;> nlinarith [hx.1, hx.2]
    have hne : d - c ≠ 0 := by linarith
    refine ⟨fun x => Γ (c + (d - c) * x), ⟨(hΓ.cont.comp (by fun_prop)).continuousOn, ?_⟩,
      by norm_num, by norm_num, ?_, ?_⟩
    · intro x hx y hy hxy
      have h := hΓ.injOn hlen' (hmem x hx) (hmem y hy) hxy
      exact mul_left_cancel₀ hne (by linarith)
    · apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩; exact ⟨_, hmem x hx, rfl⟩
      · rintro y ⟨u, hu, rfl⟩
        refine ⟨(u - c) / (d - c), ⟨div_nonneg (by linarith [hu.1]) (by linarith),
          by rw [div_le_one (by linarith)]; linarith [hu.2]⟩, ?_⟩
        change Γ (c + (d - c) * ((u - c) / (d - c))) = Γ u
        have hcancel : (d - c) * ((u - c) / (d - c)) = u - c := by field_simp
        rw [hcancel]
        congr 1
        ring
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨_, ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩, rfl⟩
  obtain ⟨γ₁, harc₁, hγ₁0, hγ₁1, himg₁, hIoo₁⟩ := key s t hst hlen
  obtain ⟨δ, harcδ, hδ0, hδ1, himgδ, hIooδ⟩ := key t (s + 1) hts1 (by linarith)
  refine ⟨γ₁, revParam δ, harc₁, harcδ.rev, hγ₁0, hγ₁1,
    by rw [revParam_zero, hδ1, hΓ.per], by rw [revParam_one, hδ0], himg₁, ?_, ?_⟩
  · rw [revParam_image, himg₁, himgδ, hΓ.image_union hst.le hts1.le]
  · rw [revParam_image_Ioo]
    refine Set.disjoint_left.2 fun x hx1 hx2 => ?_
    obtain ⟨u, hu, rfl⟩ := hIoo₁ hx1
    obtain ⟨v, hv, hvu⟩ := hIooδ hx2
    obtain ⟨n, hn⟩ := hΓ.inj hvu
    have hlt : (n : ℝ) < 1 := by rw [← hn]; linarith [hu.2, hv.1]
    have hgt : (-1 : ℝ) < n := by rw [← hn]; linarith [hu.1, hv.2]
    have hlt' : n < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n := by exact_mod_cast hgt
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    push_cast at hn
    linarith [hu.2, hv.1]

/-! ## Small Jordan subdomains -/

/-- **Small Jordan subdomains at a boundary point.**

Let `C` be a closed Jordan curve with complementary domains `D` and `E`, let `z ∈ C` and let
`ε > 0` be smaller than the distance from `z` to some point of `C`.  Then there are

* a crosscut `κ` of `D` contained in the closed disc of centre `z` and radius `ε`
  (its endpoints on `C`, its relative interior in `D`),
* the arc `γ₁` of `C` cut off by the endpoints of `κ`, also contained in that disc,
* and an open connected set `Ω ⊆ D`, contained in that disc, with
  `frontier Ω = κ ∪ γ₁`.

So every complementary domain of a closed Jordan curve contains arbitrarily small Jordan
subdomains near any prescribed point of the curve.  This is the construction underlying the
local part of **Theorem 4** of Klein–Langetepe–Nilforoushan (2009); what is *not* proved
here is that the crosscut can be chosen so that `z` lies on the small arc `γ₁`, i.e. that
`z` lies on the frontier of `Ω`. -/
theorem IsClosedJordanCurve.exists_small_crosscut_domain {C D E : Set Plane}
    (hC : IsClosedJordanCurve C) (hDo : IsOpen D) (hDconn : IsPreconnected D)
    (hEo : IsOpen E) (hdisjDE : Disjoint D E) (hunion : D ∪ E = Cᶜ)
    (hfrD : frontier D = C) {z : Plane} (hz : z ∈ C) {ε : ℝ} (hε : 0 < ε)
    (hfar : ∃ p ∈ C, ε < dist p z) :
    ∃ (κ γ₁ : ℝ → Plane) (Ω : Set Plane), IsArc κ ∧ IsArc γ₁ ∧
      κ '' Icc 0 1 ⊆ closedBall z ε ∧ γ₁ '' Icc 0 1 ⊆ C ∧ γ₁ '' Icc 0 1 ⊆ closedBall z ε ∧
      κ '' Ioo 0 1 ⊆ D ∧ κ 0 = γ₁ 0 ∧ κ 1 = γ₁ 1 ∧
      IsOpen Ω ∧ IsConnected Ω ∧ Ω ⊆ D ∧ Ω ⊆ closedBall z ε ∧
      frontier Ω = κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1 := by
  classical
  obtain ⟨Γ, hΓ⟩ := hC.exists_cyclicParam
  obtain ⟨u, hu⟩ : ∃ u, Γ u = z := by rw [← hΓ.range_eq] at hz; exact hz
  -- a short parameter interval around `u` whose image is within `ε` of `z`
  have hopen : IsOpen (Γ ⁻¹' ball z ε) := isOpen_ball.preimage hΓ.cont
  have humem : u ∈ Γ ⁻¹' ball z ε := by simp [hu, mem_ball_self hε]
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.1 hopen u humem
  set η : ℝ := min (δ / 2) (1 / 4) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by norm_num)
  have hηlt : η < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hAsub : Γ '' Icc (u - η) (u + η) ⊆ ball z ε := by
    rintro y ⟨w, hw, rfl⟩
    refine hδsub ?_
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hw.1]; linarith [hw.2]]
  -- the complementary arc, at positive distance from `z`
  set A' : Set Plane := Γ '' Icc (u + η) (u - η + 1) with hA'
  have hA'compact : IsCompact A' := (isCompact_Icc).image hΓ.cont
  have hA'ne : A'.Nonempty := ⟨Γ (u + η), ⟨u + η, ⟨le_refl _, by linarith⟩, rfl⟩⟩
  have hzA' : z ∉ A' := by
    rintro ⟨w, hw, hwz⟩
    rw [← hu] at hwz
    obtain ⟨n, hn⟩ := hΓ.inj hwz
    have h1 : (0 : ℝ) < w - u := by linarith [hw.1]
    have h2 : w - u < 1 := by linarith [hw.2]
    have h1' : (0 : ℝ) < -(n : ℝ) := by linarith [hn]
    have h2' : -(n : ℝ) < 1 := by linarith [hn]
    have hn1 : (0 : ℤ) < -n := by exact_mod_cast h1'
    have hn2 : -n < (1 : ℤ) := by exact_mod_cast h2'
    omega
  obtain ⟨y₀, hy₀A', hy₀min⟩ :=
    hA'compact.exists_isMinOn hA'ne (Continuous.continuousOn (by fun_prop : Continuous
      fun y : Plane => dist y z))
  set d : ℝ := dist y₀ z with hd
  have hdpos : 0 < d := by
    rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist y₀ z) with h | h
    · exact absurd (by rw [← dist_eq_zero.1 h.symm]; exact hy₀A' : z ∈ A') hzA'
    · exact h
  have hdmin : ∀ y ∈ A', d ≤ dist y z := fun y hy => hy₀min hy
  -- the radius of the circular crosscut
  set r : ℝ := min d ε / 2 with hr
  have hrpos : 0 < r := by
    have : 0 < min d ε := lt_min hdpos hε
    linarith
  have hrd : r < d := by
    have h1 : min d ε ≤ d := min_le_left _ _
    have : 0 < min d ε := lt_min hdpos hε
    simp only [hr]
    linarith
  have hrε : r ≤ ε := by
    have h1 : min d ε ≤ ε := min_le_right _ _
    have : 0 < min d ε := lt_min hdpos hε
    simp only [hr]
    linarith
  -- the points of `C` on the circle lie on the short arc
  have hCsplit : Γ '' Icc (u - η) (u + η) ∪ A' = C := by
    have := hΓ.image_union (a := u - η) (b := u + η) (by linarith) (by linarith)
    simpa [hA'] using this
  have honA : ∀ x ∈ C, dist x z = r → x ∈ Γ '' Icc (u - η) (u + η) := by
    intro x hx hxr
    rw [← hCsplit] at hx
    rcases hx with h | h
    · exact h
    · exact absurd hxr (by have := hdmin x h; intro hcon; rw [hcon] at this; linarith)
  -- the circular crosscut
  have hy₀C : y₀ ∈ C := by rw [← hCsplit]; exact Or.inr hy₀A'
  obtain ⟨κ₀, harc₀, hsph₀, hIoo₀, hend₀, hend₁, hne₀⟩ :=
    hC.exists_small_crosscut hDo hDconn hfrD hz hrpos hy₀C hrd
  -- parameters of the two endpoints
  obtain ⟨a, ha, hA⟩ : ∃ a ∈ Icc (u - η) (u + η), Γ a = κ₀ 0 :=
    honA _ hend₀ (hsph₀ ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩)
  obtain ⟨b, hb, hB⟩ : ∃ b ∈ Icc (u - η) (u + η), Γ b = κ₀ 1 :=
    honA _ hend₁ (hsph₀ ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩)
  have hab : a ≠ b := by
    intro h
    exact hne₀ (by rw [← hA, ← hB, h])
  -- order the endpoints so that the crosscut runs from the smaller to the larger parameter
  obtain ⟨κ, s, t, harc, hsph, hIooD, hs, ht, hst, hslo, hthi⟩ :
      ∃ (κ : ℝ → Plane) (s t : ℝ), IsArc κ ∧ κ '' Icc 0 1 ⊆ sphere z r ∧
        κ '' Ioo 0 1 ⊆ D ∧ κ 0 = Γ s ∧ κ 1 = Γ t ∧ s < t ∧
        s ∈ Icc (u - η) (u + η) ∧ t ∈ Icc (u - η) (u + η) := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨κ₀, a, b, harc₀, hsph₀, hIoo₀, hA.symm, hB.symm, h, ha, hb⟩
    · refine ⟨revParam κ₀, b, a, harc₀.rev, ?_, ?_, ?_, ?_, h, hb, ha⟩
      · rw [revParam_image]; exact hsph₀
      · rw [revParam_image_Ioo]; exact hIoo₀
      · rw [revParam_zero]; exact hB.symm
      · rw [revParam_one]; exact hA.symm
  -- the two arcs of `C` cut off by the endpoints
  obtain ⟨γ₁, γ₂, harc₁, harc₂, h₁0, h₁1, h₂0, h₂1, himg₁, hCeq, hint⟩ :=
    exists_arc_decomposition_param hΓ hst (by
      have := hslo.1; have := hslo.2; have := hthi.1; have := hthi.2; linarith)
  -- the crosscut theorem
  obtain ⟨Ω₁, Ω₂, hΩ₁o, -, hΩ₁c, -, -, hΩ₁D, -, -, -, hfΩ₁, -⟩ :=
    exists_crosscut_domains hDo hEo hdisjDE hunion harc harc₁ harc₂
      (by rw [hs, h₁0]) (by rw [ht, h₁1]) (by rw [h₂0, h₁0]) (by rw [h₂1, h₁1])
      hIooD hCeq hint
  -- the pieces are small
  have hκball : κ '' Icc 0 1 ⊆ closedBall z ε := by
    intro y hy
    have := hsph hy
    rw [mem_sphere] at this
    rw [mem_closedBall]
    linarith
  have hγ₁C : γ₁ '' Icc 0 1 ⊆ C := by rw [← hCeq]; exact subset_union_left
  have hγ₁ball : γ₁ '' Icc 0 1 ⊆ closedBall z ε := by
    rw [himg₁]
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hwmem : w ∈ Icc (u - η) (u + η) :=
      ⟨le_trans hslo.1 hw.1, le_trans hw.2 hthi.2⟩
    exact ball_subset_closedBall (hAsub ⟨w, hwmem, rfl⟩)
  -- the domain is small
  have hfrball : frontier Ω₁ ⊆ closedBall z ε := by
    rw [hfΩ₁]
    exact union_subset hκball hγ₁ball
  obtain ⟨p, hpC, hpfar⟩ := hfar
  have hpΩ : p ∉ Ω₁ := by
    intro hp
    have hpD : p ∈ D := hΩ₁D hp
    have : p ∈ Cᶜ := by rw [← hunion]; exact Or.inl hpD
    exact this hpC
  have hΩball : Ω₁ ⊆ closedBall z ε :=
    subset_closedBall_of_frontier_subset hΩ₁o hε hfrball
      (by simp only [mem_closedBall, not_le]; exact hpfar) hpΩ
  exact ⟨κ, γ₁, Ω₁, harc, harc₁, hκball, hγ₁C, hγ₁ball, hIooD, by rw [hs, h₁0],
    by rw [ht, h₁1], hΩ₁o, hΩ₁c, hΩ₁D, hΩball, hfΩ₁⟩

end AVD
