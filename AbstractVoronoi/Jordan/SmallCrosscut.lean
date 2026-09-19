import AbstractVoronoi.Jordan.CircularCrosscut
import AbstractVoronoi.Jordan.CyclicParam

/-!
# Crosscuts of small diameter

This file turns the circular arcs of `AbstractVoronoi.Jordan.CircularCrosscut` into genuine
*crosscuts of small diameter* of a complementary domain of a closed Jordan curve.

The main result, `AVD.IsClosedJordanCurve.exists_small_crosscut`, says: if `C` is a closed
Jordan curve, `D` a complementary domain of it (an open connected set with `frontier D = C`),
`z ∈ C` and `r > 0` is smaller than the distance from `z` to some point of `C`, then `D` has
a crosscut contained in the circle of centre `z` and radius `r` — an arc with distinct
endpoints on `C`, relative interior inside `D`, and diameter at most `2r`.  Choosing `r`
small therefore produces crosscuts of arbitrarily small diameter near `z`, and choosing `r`
smaller than the distance from `z` to the complement of a subarc `A ∋ z` of `C` forces the
endpoints of the crosscut to lie on `A` (`AVD.IsClosedJordanCurve.exists_small_crosscut_in`).

These are the small crosscuts required by the local (Jordan–Schönflies) part of **Theorem 4**
of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- A preconnected set of the plane having a point inside and a point outside the circle of
centre `z` and radius `r` meets that circle. -/
theorem exists_mem_sphere_of_preconnected {K : Set Plane} (hK : IsPreconnected K)
    {z : Plane} {r : ℝ} {a b : Plane} (ha : a ∈ K) (hb : b ∈ K)
    (hal : dist a z < r) (hbg : r < dist b z) : ∃ q ∈ K, dist q z = r := by
  by_contra hcon
  push Not at hcon
  set U : Set Plane := {x : Plane | dist x z < r} with hU
  set V : Set Plane := {x : Plane | r < dist x z} with hV
  have hUopen : IsOpen U := isOpen_lt (continuous_id.dist continuous_const) continuous_const
  have hVopen : IsOpen V := isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hdisj : Disjoint U V := by
    refine Set.disjoint_left.2 fun x hx hxV => ?_
    have h1 : dist x z < r := hx
    have h2 : r < dist x z := hxV
    linarith
  have hsub : K ⊆ U ∪ V := by
    intro x hx
    rcases lt_trichotomy (dist x z) r with h | h | h
    · exact Or.inl h
    · exact absurd h (hcon x hx)
    · exact Or.inr h
  have hleft : K ⊆ U := hK.subset_left_of_subset_union hUopen hVopen hdisj hsub ⟨a, ha, hal⟩
  have hbU : dist b z < r := hleft hb
  linarith

/-- A closed Jordan curve is preconnected. -/
theorem IsClosedJordanCurve.isPreconnected {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : IsClosedJordanCurve C) : IsPreconnected C := by
  obtain ⟨γ, hcont, -, -, himg⟩ := hC
  rw [← himg]
  exact isPreconnected_Icc.image γ hcont

/-- A closed Jordan curve minus one of its points is still preconnected: it is the
homeomorphic image of an open arc of the circle. -/
theorem IsClosedJordanCurve.isPreconnected_diff_singleton {X : Type*} [TopologicalSpace X]
    {C : Set X} (hC : IsClosedJordanCurve C) {q : X} (hq : q ∈ C) :
    IsPreconnected (C \ {q}) := by
  obtain ⟨Γ, hΓ⟩ := hC.exists_cyclicParam
  obtain ⟨s, hs⟩ : ∃ s, Γ s = q := by rw [← hΓ.range_eq] at hq; exact hq
  have hEq : C \ {q} = Γ '' Ioo s (s + 1) := by
    apply Subset.antisymm
    · rintro y ⟨hyC, hyq⟩
      rw [← hΓ.image_Icc s] at hyC
      obtain ⟨t, ht, rfl⟩ := hyC
      have hts : t ≠ s := by
        rintro rfl
        exact hyq (by simp [hs])
      have hts1 : t ≠ s + 1 := by
        rintro rfl
        exact hyq (by rw [mem_singleton_iff, ← hs, hΓ.per])
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hts), lt_of_le_of_ne ht.2 hts1⟩, rfl⟩
    · rintro y ⟨t, ht, rfl⟩
      refine ⟨by rw [← hΓ.range_eq]; exact mem_range_self t, ?_⟩
      rw [mem_singleton_iff, ← hs]
      intro heq
      obtain ⟨n, hn⟩ := hΓ.inj heq
      have h1 : (-1 : ℝ) < n := by rw [← hn]; linarith [ht.2]
      have h2 : (n : ℝ) < 0 := by rw [← hn]; linarith [ht.1]
      have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
      have h2' : n < 0 := by exact_mod_cast h2
      omega
  rw [hEq]
  exact isPreconnected_Ioo.image _ hΓ.cont.continuousOn

/-- A closed Jordan curve through the centre of a circle which has a point outside the
circle meets that circle in at least two points.

(One intersection point is produced by connectedness; a second one by connectedness of the
curve with the first point removed.) -/
theorem IsClosedJordanCurve.nontrivial_sphere_inter {C : Set Plane}
    (hC : IsClosedJordanCurve C) {z : Plane} (hz : z ∈ C) {r : ℝ} (hr : 0 < r)
    {p : Plane} (hp : p ∈ C) (hpr : r < dist p z) : (C ∩ sphere z r).Nontrivial := by
  obtain ⟨q, hqC, hq⟩ :=
    exists_mem_sphere_of_preconnected hC.isPreconnected hz hp (by simpa using hr) hpr
  have hzq : z ≠ q := by
    intro h
    rw [← h, dist_self] at hq
    linarith
  have hpq : p ≠ q := by
    intro h
    rw [h, hq] at hpr
    exact lt_irrefl r hpr
  obtain ⟨q', hq'C, hq'⟩ :=
    exists_mem_sphere_of_preconnected (hC.isPreconnected_diff_singleton hqC)
      ⟨hz, hzq⟩ ⟨hp, hpq⟩ (by simpa using hr) hpr
  refine ⟨q, ⟨hqC, hq⟩, q', ⟨hq'C.1, hq'⟩, ?_⟩
  intro h
  exact hq'C.2 (by rw [← h]; rfl)

/-- **Crosscuts of small diameter.**

Let `C` be a closed Jordan curve, let `D` be a complementary domain of it (an open connected
set with `frontier D = C`), let `z ∈ C` and let `r > 0` be smaller than the distance from `z`
to some point of `C`.  Then `D` has a *crosscut* contained in the circle of centre `z` and
radius `r`: an arc `κ` with distinct endpoints on `C`, whose relative interior lies in `D`,
and which is contained in the circle — so its diameter is at most `2r`.

Crosscuts of arbitrarily small diameter near a point of the curve are the missing
ingredient of the local part of **Theorem 4** of Klein–Langetepe–Nilforoushan (2009). -/
theorem IsClosedJordanCurve.exists_small_crosscut {C D : Set Plane}
    (hC : IsClosedJordanCurve C) (hDo : IsOpen D) (hDconn : IsPreconnected D)
    (hfr : frontier D = C) {z : Plane} (hz : z ∈ C) {r : ℝ} (hr : 0 < r)
    {p : Plane} (hp : p ∈ C) (hpr : r < dist p z) :
    ∃ κ : ℝ → Plane, IsArc κ ∧ κ '' Icc 0 1 ⊆ sphere z r ∧ κ '' Ioo 0 1 ⊆ D ∧
      κ 0 ∈ C ∧ κ 1 ∈ C ∧ κ 0 ≠ κ 1 := by
  have hDC : Disjoint D C := by
    rw [← hfr, hDo.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  -- two points of the circle outside `D`
  have h2 : (sphere z r \ D).Nontrivial := by
    obtain ⟨q₁, hq₁, q₂, hq₂, hne⟩ := hC.nontrivial_sphere_inter hz hr hp hpr
    exact ⟨q₁, ⟨hq₁.2, fun h => (Set.disjoint_left.1 hDC) h hq₁.1⟩,
      q₂, ⟨hq₂.2, fun h => (Set.disjoint_left.1 hDC) h hq₂.1⟩, hne⟩
  -- a point of `D` inside the circle, and one outside
  have hzcl : z ∈ closure D := by rw [← hfr] at hz; exact frontier_subset_closure hz
  obtain ⟨a, haD, haball⟩ : ∃ a ∈ D, dist a z < r := by
    obtain ⟨a, haball, haD⟩ := mem_closure_iff.1 hzcl (ball z r) isOpen_ball (mem_ball_self hr)
    exact ⟨a, haD, Metric.mem_ball.1 haball⟩
  have hpcl : p ∈ closure D := by rw [← hfr] at hp; exact frontier_subset_closure hp
  obtain ⟨b, hbD, hbfar⟩ : ∃ b ∈ D, r < dist b z := by
    obtain ⟨b, hbball, hbD⟩ := mem_closure_iff.1 hpcl (ball p (dist p z - r)) isOpen_ball
      (mem_ball_self (by linarith))
    refine ⟨b, hbD, ?_⟩
    have h1 : dist b p < dist p z - r := Metric.mem_ball.1 hbball
    have h2 : dist p z ≤ dist p b + dist b z := dist_triangle p b z
    have h3 : dist p b = dist b p := dist_comm p b
    linarith
  obtain ⟨w, hwD, hw⟩ := exists_mem_sphere_of_preconnected hDconn haD hbD haball hbfar
  obtain ⟨κ, harc, hsph, hIoo, -, h0, h1, hne⟩ :=
    exists_circular_crosscut hDo hr hwD hw h2
  exact ⟨κ, harc, hsph, hIoo, by rwa [hfr] at h0, by rwa [hfr] at h1, hne⟩

/-- Small crosscuts with endpoints on a prescribed part of the curve.

If in addition `A ⊆ C` is such that all points of `C` at distance `r` from `z` belong to
`A` — which holds as soon as `r` is smaller than the distance from `z` to `C ∖ A` — then the
endpoints of the crosscut produced by
`AVD.IsClosedJordanCurve.exists_small_crosscut` lie on `A`. -/
theorem IsClosedJordanCurve.exists_small_crosscut_in {C D A : Set Plane}
    (hC : IsClosedJordanCurve C) (hDo : IsOpen D) (hDconn : IsPreconnected D)
    (hfr : frontier D = C) {z : Plane} (hz : z ∈ C) {r : ℝ} (hr : 0 < r)
    {p : Plane} (hp : p ∈ C) (hpr : r < dist p z)
    (hA : ∀ x ∈ C, dist x z = r → x ∈ A) :
    ∃ κ : ℝ → Plane, IsArc κ ∧ κ '' Icc 0 1 ⊆ sphere z r ∧ κ '' Ioo 0 1 ⊆ D ∧
      κ 0 ∈ A ∧ κ 1 ∈ A ∧ κ 0 ≠ κ 1 := by
  obtain ⟨κ, harc, hsph, hIoo, h0, h1, hne⟩ :=
    hC.exists_small_crosscut hDo hDconn hfr hz hr hp hpr
  have hm0 : κ 0 ∈ sphere z r := hsph ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have hm1 : κ 1 ∈ sphere z r := hsph ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
  exact ⟨κ, harc, hsph, hIoo, hA _ h0 hm0, hA _ h1 hm1, hne⟩

end AVD
