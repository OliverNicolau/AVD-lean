import AbstractVoronoi.Jordan.ArcFacts
import AbstractVoronoi.Jordan.Backend

/-!
# Accessible points of a closed Jordan curve

This file proves the accessibility of the points of a closed Jordan curve `C` from its two
complementary domains, which is the *local* assertion of **Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902:

> Point `z` is accessible from each domain `U ∩ Dᵢ`, that is, for each `p ∈ U ∩ Dᵢ` there
> exists an arc `α` from `p` to `z` such that `α` minus its endpoint `z` belongs to
> `U ∩ Dᵢ`.

The statement proved here is the global form of that assertion: *every* point `p` of a
complementary domain `D₁` of `C` is joined to *every* point `z` of `C` by an arc which,
apart from its endpoint `z`, runs inside `D₁` (`AVD.IsClosedJordanCurve.accessibleWithin`).
Its ingredients are the local structure of the curve
(`AVD.jordanCurveLocalStructure`, which rests on the Jordan–Schönflies theorem of the
dependency through `AVD.jordanCurveLocalConnectedness`) and the arc surgery of
`AbstractVoronoi.Jordan.ArcFacts`, which joins an arbitrary point of the domain to the access
arc supplied by the local structure.

Three consequences are recorded, in the approximate forms in which they are often used: the
endpoint of an access arc can be prescribed to lie on any preassigned subarc of `C`
(`AVD.IsClosedJordanCurve.exists_access_arc_in_subarc`), arbitrarily close to a prescribed
point of `C` (`AVD.IsClosedJordanCurve.exists_access_arc_near`), so that the accessible
points are dense in `C` (`AVD.IsClosedJordanCurve.dense_accessible`).
-/

noncomputable section

open Set Topology

namespace AVD

/-! ## Separation of two points of different complementary domains -/

/-- Two points lying in different complementary domains of a closed Jordan curve `C` cannot
be joined by an arc avoiding `C`. -/
theorem inter_nonempty_of_mem_domains {C : Set Plane} {D₁ D₂ : Set Plane}
    (h1o : IsOpen D₁) (h2o : IsOpen D₂) (hdisj : Disjoint D₁ D₂) (hunion : D₁ ∪ D₂ = Cᶜ)
    {p q : Plane} (hp : p ∈ D₁) (hq : q ∈ D₂) {B : Set Plane}
    (hB : Backend.IsArcBetween B p q) : (B ∩ C).Nonempty := by
  obtain ⟨f, hcont, -, hBf, h0, h1⟩ := hB
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  have hBC : B ⊆ D₁ ∪ D₂ := by
    rw [hunion]
    intro x hx
    exact fun hxC => absurd (show x ∈ B ∩ C from ⟨hx, hxC⟩) (by rw [hcon]; exact id)
  have hpre : IsPreconnected B := by
    rw [← hBf]
    exact (isPreconnected_Icc).image f hcont
  have hBsub : B ⊆ D₁ :=
    hpre.subset_left_of_subset_union h1o h2o hdisj hBC
      ⟨p, by rw [← hBf, ← h0]; exact ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩, hp⟩
  have : q ∈ D₁ := hBsub (by rw [← hBf, ← h1]; exact ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩)
  exact (Set.disjoint_left.1 hdisj this) hq

/-! ## Small subarcs around a point of the curve -/

/-- Every point `z` of a closed Jordan curve `C` is an interior point of arbitrarily small
subarcs of `C`.  This is the form in which the curve is cut in the proof of **Theorem 4** of
Klein–Langetepe–Nilforoushan (2009) ("we can make `U` small enough"). -/
theorem IsClosedJordanCurve.exists_subarc_near {C : Set Plane} (hC : IsClosedJordanCurve C)
    {z : Plane} (hz : z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : Set Plane) (v w : Plane), Backend.IsArcBetween A v w ∧ A ⊆ C ∧ z ∈ A ∧
      z ≠ v ∧ z ≠ w ∧ A ⊆ Metric.ball z ε := by
  obtain ⟨Γ, hΓ⟩ := hC.exists_cyclicParam
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, Γ t₀ = z := by rw [← hΓ.range_eq] at hz; exact hz
  obtain ⟨η, hη, hηsub⟩ : ∃ η > (0 : ℝ), ∀ t, |t - t₀| < η → Γ t ∈ Metric.ball z ε := by
    have hcontat : ContinuousAt Γ t₀ := hΓ.cont.continuousAt
    have h := Metric.tendsto_nhds.1 hcontat ε hε
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨η, hη, hsub⟩ := h
    refine ⟨η, hη, fun t htt => ?_⟩
    have hd : dist t t₀ < η := by rwa [Real.dist_eq]
    have h2 := hsub hd
    rw [ht₀] at h2
    exact Metric.mem_ball.2 h2
  set δ : ℝ := min (η / 2) (1 / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδη : δ < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  set a := t₀ - δ with ha
  set b := t₀ + δ with hb
  have hab : a < b := by simp [ha, hb]; linarith
  have hlen : b - a < 1 := by simp [ha, hb]; linarith
  obtain ⟨κ, hκcont, hκinj, hκ0, hκ1, hκimg⟩ := hΓ.exists_param_Icc hab hlen
  refine ⟨Γ '' Icc a b, Γ a, Γ b, ⟨κ, hκcont.continuousOn, hκinj, hκimg, hκ0, hκ1⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨s, -, rfl⟩
    rw [← hΓ.range_eq]; exact mem_range_self s
  · exact ⟨t₀, ⟨by linarith, by linarith⟩, ht₀⟩
  · intro h
    have := hΓ.injOn hlen (show t₀ ∈ Icc a b from ⟨by linarith, by linarith⟩)
      (show a ∈ Icc a b from ⟨le_refl a, hab.le⟩) (by rw [ht₀]; exact h)
    simp [ha] at this; linarith
  · intro h
    have := hΓ.injOn hlen (show t₀ ∈ Icc a b from ⟨by linarith, by linarith⟩)
      (show b ∈ Icc a b from ⟨hab.le, le_refl b⟩) (by rw [ht₀]; exact h)
    simp [hb] at this; linarith
  · rintro y ⟨s, hs, rfl⟩
    refine hηsub s ?_
    rw [abs_lt]
    constructor
    · have := hs.1; simp [ha] at this ⊢; linarith
    · have := hs.2; simp [hb] at this ⊢; linarith

/-! ## Accessibility of the points of the curve -/

/-- **Accessibility of the points of a closed Jordan curve**, the local assertion of
**Theorem 4** of Klein–Langetepe–Nilforoushan (2009) in its global form: every point `z` of
the curve is joined to every point `p` of a complementary domain `D₁` by an arc which, apart
from its endpoint `z`, runs inside `D₁`.

The proof combines the local structure of the curve at `z` (`AVD.jordanCurveLocalStructure`,
which rests on the Jordan–Schönflies theorem) with the arc surgery
`AVD.exists_arc_of_accessible`, which joins `p` to the access arc inside `D₁`. -/
theorem IsClosedJordanCurve.accessibleWithin {C D₁ D₂ : Set Plane}
    (hC : IsClosedJordanCurve C) (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (h1c : IsConnected D₁) (h2c : IsConnected D₂) (hdisj : Disjoint D₁ D₂)
    (hunion : D₁ ∪ D₂ = Cᶜ) (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    {z : Plane} (hz : z ∈ C) {p : Plane} (hp : p ∈ D₁) :
    AccessibleWithin D₁ p z := by
  -- the local structure of the curve at `z`
  obtain ⟨U, -, -, -, hUc1, -, hacc1, -⟩ :=
    jordanCurveLocalStructure C (Or.inl hC) D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 z hz
      univ Filter.univ_mem
  obtain ⟨x, hx⟩ := hUc1.nonempty
  have hzacc : AccessibleFrom D₁ z :=
    (AccessibleFrom.of_within (hacc1 x hx)).mono inter_subset_right
  -- `p` lies in the open set `D₁`, and `z` does not
  have hzD : z ∉ D₁ := by
    have : z ∈ Cᶜᶜ := by simpa using hz
    rw [← hunion] at this
    exact fun hcon => this (Or.inl hcon)
  have hpz : p ≠ z := fun h => hzD (h ▸ hp)
  have hconn : ∀ x ∈ D₁, ∀ y ∈ D₁, JoinedIn D₁ x y :=
    (h1o.isConnected_iff_isPathConnected.1 h1c).joinedIn
  obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ :=
    exists_arc_of_accessible h1o hconn hpz (accessible_of_mem_open h1o hp) hzacc
  refine ⟨γ, hγ, hγ0, hγ1, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0, hγ0]; exact hp
  · exact hγsub ⟨t, ⟨h0, ht.2⟩, rfl⟩

/-- **Access to a prescribed subarc of a closed Jordan curve.**

Let `C` be a closed Jordan curve with complementary domains `D₁`, `D₂`, let `A ⊆ C` be a
subarc of `C` and let `x` be a point of `A`.  Then every point `p ∈ D₁` is joined by an arc,
running inside `D₁` up to its endpoint, to a point of `A`.

This is a corollary of `AVD.IsClosedJordanCurve.accessibleWithin`: the endpoint can be taken
to be `x` itself. -/
theorem IsClosedJordanCurve.exists_access_arc_in_subarc {C : Set Plane}
    (hC : IsClosedJordanCurve C) {D₁ D₂ : Set Plane} (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (h1c : IsConnected D₁) (h2c : IsConnected D₂) (hdisj : Disjoint D₁ D₂)
    (hunion : D₁ ∪ D₂ = Cᶜ) (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    {A : Set Plane} {x : Plane} (hAsub : A ⊆ C) (hx : x ∈ A)
    {p : Plane} (hp : p ∈ D₁) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = p ∧ γ 1 ∈ A ∧ γ '' Ico 0 1 ⊆ D₁ := by
  obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ :=
    hC.accessibleWithin h1o h2o h1c h2c hdisj hunion hf1 hf2 (hAsub hx) hp
  exact ⟨γ, hγ, hγ0, by rw [hγ1]; exact hx, hγsub⟩

/-- **Accessibility of the points of a closed Jordan curve, in approximate form.**

For every point `z` of a closed Jordan curve `C`, every point `p` of a complementary domain
`D₁` of `C` and every `ε > 0`, there is an arc starting at `p`, running inside `D₁` up to
its endpoint, whose endpoint lies on `C` at distance less than `ε` from `z`.  (In fact the
endpoint may be taken to be `z` itself, by
`AVD.IsClosedJordanCurve.accessibleWithin`.) -/
theorem IsClosedJordanCurve.exists_access_arc_near {C : Set Plane}
    (hC : IsClosedJordanCurve C) {D₁ D₂ : Set Plane} (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (h1c : IsConnected D₁) (h2c : IsConnected D₂) (hdisj : Disjoint D₁ D₂)
    (hunion : D₁ ∪ D₂ = Cᶜ) (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    {z : Plane} (hz : z ∈ C) {p : Plane} (hp : p ∈ D₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = p ∧ γ 1 ∈ C ∧ dist (γ 1) z < ε ∧ γ '' Ico 0 1 ⊆ D₁ := by
  obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ :=
    hC.accessibleWithin h1o h2o h1c h2c hdisj hunion hf1 hf2 hz hp
  exact ⟨γ, hγ, hγ0, by rw [hγ1]; exact hz, by rw [hγ1]; simpa using hε, hγsub⟩

/-- **The points of a closed Jordan curve that are accessible from a complementary domain
are dense in the curve** — indeed all of them are accessible.

This is the accessibility assertion of **Theorem 4** of Klein–Langetepe–Nilforoushan (2009),
stated with the notion of accessibility of the paper (`AVD.AccessibleFrom`, used in
Lemma 8). -/
theorem IsClosedJordanCurve.dense_accessible {C : Set Plane}
    (hC : IsClosedJordanCurve C) {D₁ D₂ : Set Plane} (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (h1c : IsConnected D₁) (h2c : IsConnected D₂) (hdisj : Disjoint D₁ D₂)
    (hunion : D₁ ∪ D₂ = Cᶜ) (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    {z : Plane} (hz : z ∈ C) : AccessibleFrom D₁ z := by
  obtain ⟨p, hp⟩ := h1c.nonempty
  exact AccessibleFrom.of_within (hC.accessibleWithin h1o h2o h1c h2c hdisj hunion hf1 hf2 hz hp)

end AVD
