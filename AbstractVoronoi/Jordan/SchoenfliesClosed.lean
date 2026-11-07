import AbstractVoronoi.Jordan.LocallyConnectedTransfer
import AbstractVoronoi.Jordan.Schoenflies
import AbstractVoronoi.Jordan.Backend

/-!
# The local structure of a closed Jordan curve, from the Jordan–Schönflies theorem

This file proves, for a **closed** Jordan curve `C` of the plane and its two complementary
domains `D₁`, `D₂`, that each domain is locally connected at every point of the curve
(`AVD.IsClosedJordanCurve.locallyConnectedAt`).  This is the Jordan–Schönflies content of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902, **Theorem 4**,

in the form in which the rest of this development uses it.

The proof is the classical one, and it is short because the dependency supplies the
Jordan–Schönflies theorem itself: by `Backend.jordan_schoenflies_of_homeomorph` there is
a homeomorphism `F` of the plane carrying `C` onto the model curve `∂Q` (the boundary of the
square `Q = [-1,1]²`), and `F` then carries `D₁` and `D₂` onto the two complementary domains
of `∂Q`, namely the open square and the complement of the closed square.  For those two
explicit sets local connectedness is elementary: the open square is convex, and the exterior
of the square is joined near a boundary point by pushing the two points radially outwards and
joining them by a segment (`AVD.locallyConnectedAt_compl_closedSquare`).
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-! ## The sup norm of the plane -/

/-- The sup norm is homogeneous. -/
theorem supNorm_smul (c : ℝ) (x : Plane) :
    Square.supNorm (c • x) = |c| * Square.supNorm x := by
  simp only [Square.supNorm, PiLp.smul_apply, smul_eq_mul, abs_mul]
  exact (mul_max_of_nonneg _ _ (abs_nonneg c)).symm

/-- A point at distance at most `δ` from a point of the model curve has sup norm at least
`1 - δ`. -/
theorem one_sub_le_supNorm {w x : Plane} (hw : Square.supNorm w = 1) {δ : ℝ}
    (h : dist x w ≤ δ) : 1 - δ ≤ Square.supNorm x := by
  have htri := Square.supDist_triangle w x 0
  have h1 : Square.supDist w 0 = Square.supNorm w := by
    simp [Square.supDist]
  have h2 : Square.supDist x 0 = Square.supNorm x := by
    simp [Square.supDist]
  have h3 : Square.supDist w x ≤ dist w x :=
    Square.supNorm_le_norm (w - x)
  rw [h1, h2, hw] at htri
  rw [dist_comm] at h
  linarith

/-- The norm of a point of the plane is at most `3/2` times its sup norm. -/
theorem norm_le_three_halves_mul_supNorm (x : Plane) :
    ‖x‖ ≤ 3 / 2 * Square.supNorm x := by
  have h := Square.norm_le_sqrt_two_mul_supNorm x
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ)/2 = Real.sqrt ((3/2)^2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [Square.supNorm_nonneg x]

/-- Membership in the complement of the closed unit square, in terms of the sup norm. -/
theorem mem_compl_closedSquare_iff {x : Plane} :
    x ∈ (Square.closedSquare 0 1)ᶜ ↔ 1 < Square.supNorm x := by
  simp [Square.closedSquare, Square.supDist]

/-- Membership in the open unit square, in terms of the sup norm. -/
theorem mem_openSquare_iff {x : Plane} :
    x ∈ Square.openSquare 0 1 ↔ Square.supNorm x < 1 := by
  simp [Square.openSquare, Square.supDist]

/-! ## Local connectedness of the two complementary domains of the model curve -/

/-- The open square is convex, hence locally connected at each point of the plane. -/
theorem locallyConnectedAt_openSquare (w : Plane) :
    LocallyConnectedAt (Square.openSquare 0 1) w := by
  intro ε hε
  refine ⟨ε, hε, fun x hx y hy => ?_⟩
  refine joinedIn_of_segment_subset ?_
  have hconv : Convex ℝ (Square.openSquare 0 1 ∩ ball w ε) :=
    (Square.convex_openSquare 1).inter (convex_ball w ε)
  exact hconv.segment_subset hx hy

/-- **The exterior of the square is locally connected at each point of the model curve.**
Two points of the exterior close to a point `w` of the curve are joined inside the exterior,
and close to `w`, by pushing both radially outwards by the factor `1 + 2δ` and joining the
two pushed points by a segment: the segment stays outside the square because all the points
involved have sup norm at least `1 - δ`, and it stays close to `w` because everything in
sight has norm at most `2`. -/
theorem locallyConnectedAt_compl_closedSquare {w : Plane}
    (hw : Square.supNorm w = 1) :
    LocallyConnectedAt ((Square.closedSquare 0 1)ᶜ) w := by
  intro ε hε
  set δ : ℝ := min (ε / 6) (1 / 4) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 6 := min_le_left _ _
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  set s : ℝ := 1 + 2 * δ with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; linarith
  -- the sup norm and the norm of a point close to `w`
  have hball : ∀ m : Plane, dist m w ≤ δ → 1 - δ ≤ Square.supNorm m := by
    intro m hm
    exact one_sub_le_supNorm hw hm
  have hnormw : ‖w‖ ≤ 3 / 2 := by
    have := norm_le_three_halves_mul_supNorm w
    rw [hw] at this; linarith
  have hnorm : ∀ m : Plane, dist m w ≤ δ → ‖m‖ ≤ 2 := by
    intro m hm
    have h := dist_triangle m w 0
    simp only [dist_zero_right] at h
    linarith
  -- a scaled point far enough from the origin stays outside the square and close to `w`
  have hkey : ∀ (m : Plane) (c : ℝ), dist m w ≤ δ → 1 - δ ≤ Square.supNorm m →
      1 ≤ c → c ≤ s → (1 : ℝ) < c * Square.supNorm m →
      c • m ∈ (Square.closedSquare 0 1)ᶜ ∩ ball w ε := by
    intro m c hm _ hc1 hcs hgt
    constructor
    · rw [mem_compl_closedSquare_iff, supNorm_smul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c)]
      exact hgt
    · have hdist : dist (c • m) w ≤ ‖c • m - m‖ + dist m w := by
        have := dist_triangle (c • m) m w
        simpa [dist_eq_norm] using this
      have hcm : ‖c • m - m‖ = (c - 1) * ‖m‖ := by
        rw [show c • m - m = (c - 1) • m by module, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - 1)]
      have hmnorm : ‖m‖ ≤ 2 := hnorm m hm
      have hc : c - 1 ≤ 2 * δ := by rw [hsdef] at hcs; linarith
      have : dist (c • m) w ≤ 2 * δ * 2 + δ := by
        rw [hcm] at hdist
        nlinarith [norm_nonneg m, hm]
      have hfin : dist (c • m) w < ε := by nlinarith
      exact mem_ball.2 hfin
  -- the three segments of the path
  have hxb : dist x w ≤ δ := le_of_lt (mem_ball.1 hx.2)
  have hyb : dist y w ≤ δ := le_of_lt (mem_ball.1 hy.2)
  have hxs : 1 < Square.supNorm x := mem_compl_closedSquare_iff.1 hx.1
  have hys : 1 < Square.supNorm y := mem_compl_closedSquare_iff.1 hy.1
  have hseg₁ : JoinedIn ((Square.closedSquare 0 1)ᶜ ∩ ball w ε) x (s • x) := by
    refine joinedIn_of_segment_subset ?_
    rintro p ⟨a, b, ha, hb, hab, rfl⟩
    have hp : a • x + b • (s • x) = (a + b * s) • x := by
      rw [smul_smul, ← add_smul]
    rw [hp]
    have hc1 : 1 ≤ a + b * s := by nlinarith
    refine hkey x (a + b * s) hxb (hball x hxb) hc1 (by nlinarith) ?_
    calc (1 : ℝ) < Square.supNorm x := hxs
      _ = 1 * Square.supNorm x := (one_mul _).symm
      _ ≤ (a + b * s) * Square.supNorm x :=
          mul_le_mul_of_nonneg_right hc1 (by linarith)
  have hseg₃ : JoinedIn ((Square.closedSquare 0 1)ᶜ ∩ ball w ε) (s • y) y := by
    refine JoinedIn.symm (joinedIn_of_segment_subset ?_)
    rintro p ⟨a, b, ha, hb, hab, rfl⟩
    have hp : a • y + b • (s • y) = (a + b * s) • y := by
      rw [smul_smul, ← add_smul]
    rw [hp]
    have hc1 : 1 ≤ a + b * s := by nlinarith
    refine hkey y (a + b * s) hyb (hball y hyb) hc1 (by nlinarith) ?_
    calc (1 : ℝ) < Square.supNorm y := hys
      _ = 1 * Square.supNorm y := (one_mul _).symm
      _ ≤ (a + b * s) * Square.supNorm y :=
          mul_le_mul_of_nonneg_right hc1 (by linarith)
  have hseg₂ : JoinedIn ((Square.closedSquare 0 1)ᶜ ∩ ball w ε) (s • x) (s • y) := by
    refine joinedIn_of_segment_subset ?_
    rintro p ⟨a, b, ha, hb, hab, rfl⟩
    have hp : a • (s • x) + b • (s • y) = s • (a • x + b • y) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_comm a s, mul_comm b s]
    rw [hp]
    set m : Plane := a • x + b • y with hm
    have hmball : dist m w ≤ δ := by
      have hconv : Convex ℝ (closedBall w δ) := convex_closedBall w δ
      have : m ∈ closedBall w δ :=
        hconv (mem_closedBall.2 hxb) (mem_closedBall.2 hyb) ha hb hab
      exact mem_closedBall.1 this
    have hmsup : 1 - δ ≤ Square.supNorm m := hball m hmball
    refine hkey m s hmball hmsup hs1 le_rfl ?_
    have hpos : 0 < 1 - δ := by linarith
    nlinarith
  exact (hseg₁.trans hseg₂).trans hseg₃

/-! ## Transferring the Jordan–Schönflies theorem -/

/-- **A closed Jordan curve can be carried onto the model curve by a homeomorphism of the
plane.**  This is the Jordan–Schönflies theorem of the dependency
(`Backend.jordan_schoenflies_of_homeomorph`), applied to a homeomorphism between the
curve and the model curve. -/
theorem IsClosedJordanCurve.exists_planeHomeomorph_image_eq_modelCurve {C : Set Plane}
    (hC : IsClosedJordanCurve C) :
    ∃ F : Plane ≃ₜ Plane, F '' C = Square.modelCurve := by
  have hCJ : Backend.IsJordanCurve C := isClosedJordanCurve_iff.1 hC
  obtain ⟨e⟩ := hCJ.nonempty_homeomorph_modelCurve
  obtain ⟨F, hF⟩ :=
    Backend.jordan_schoenflies_of_homeomorph hCJ Backend.isJordanCurve_modelCurve e
  refine ⟨F, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hF ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(e.symm ⟨y, hy⟩ : Plane), (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [hF (e.symm ⟨y, hy⟩)]
    simp

/-- **The complementary domains of a closed Jordan curve are locally connected at the points
of the curve.**

This is the Jordan–Schönflies content of Theorem 4 of Klein–Langetepe–Nilforoushan (2009), in
the form used in this development: carry `C` onto the model curve by a homeomorphism `F` of
the plane; `F` carries `D₁` onto one of the two complementary domains of the model curve,
each of which is locally connected at each point of that curve. -/
theorem IsClosedJordanCurve.locallyConnectedAt {C D₁ D₂ : Set Plane}
    (hC : IsClosedJordanCurve C) (h1c : IsConnected D₁) (h2c : IsConnected D₂)
    (hunion : D₁ ∪ D₂ = Cᶜ) {z : Plane} (hz : z ∈ C) :
    LocallyConnectedAt D₁ z := by
  obtain ⟨F, hFC⟩ := hC.exists_planeHomeomorph_image_eq_modelCurve
  set U : Set Plane := Square.openSquare 0 1 with hU
  set E : Set Plane := (Square.closedSquare 0 1)ᶜ with hE
  -- the complement of the model curve is the union of the two open squares
  have hcompl : (Square.modelCurve)ᶜ = U ∪ E := Square.compl_modelCurve
  have hUopen : IsOpen U := Square.isOpen_openSquare 1
  have hEopen : IsOpen E := (Square.isClosed_closedSquare 1).isOpen_compl
  have hUE : Disjoint U E := by
    rw [Set.disjoint_left]
    intro p hp hp'
    rw [hU, mem_openSquare_iff] at hp
    rw [hE, mem_compl_closedSquare_iff] at hp'
    linarith
  -- the images of the two domains
  have himg : F '' D₁ ∪ F '' D₂ = U ∪ E := by
    rw [← Set.image_union, hunion, Set.image_compl_eq F.bijective, hFC, hcompl]
  have h1sub : F '' D₁ ⊆ U ∪ E := by rw [← himg]; exact subset_union_left
  have h2sub : F '' D₂ ⊆ U ∪ E := by rw [← himg]; exact subset_union_right
  have h1conn : IsPreconnected (F '' D₁) := h1c.isPreconnected.image _ F.continuous.continuousOn
  have h2conn : IsPreconnected (F '' D₂) := h2c.isPreconnected.image _ F.continuous.continuousOn
  have h1or := h1conn.subset_or_subset hUopen hEopen hUE h1sub
  have h2or := h2conn.subset_or_subset hUopen hEopen hUE h2sub
  -- the exterior of the square is nonempty, and so is the open square
  have hEne : E.Nonempty := by
    refine ⟨(2 : ℝ) • (EuclideanSpace.single 0 1 : Plane), ?_⟩
    rw [hE, mem_compl_closedSquare_iff, supNorm_smul]
    have h1 : Square.supNorm (EuclideanSpace.single 0 1 : Plane) = 1 := by
      simp [Square.supNorm]
    rw [h1]
    norm_num
  have hUne : U.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hU, mem_openSquare_iff]
    simp [Square.supNorm]
  -- `F '' D₁` is one of the two domains of the model curve
  have hFz : Square.supNorm (F z) = 1 := by
    have : F z ∈ Square.modelCurve := by rw [← hFC]; exact ⟨z, hz, rfl⟩
    exact this
  have hmain : F '' D₁ = U ∨ F '' D₁ = E := by
    rcases h1or with h1 | h1
    · rcases h2or with h2 | h2
      · exfalso
        obtain ⟨p, hp⟩ := hEne
        have : p ∈ U := by
          have hpUE : p ∈ U ∪ E := Or.inr hp
          rw [← himg] at hpUE
          rcases hpUE with hq | hq
          · exact h1 hq
          · exact h2 hq
        exact (Set.disjoint_left.1 hUE this) hp
      · refine Or.inl (Subset.antisymm h1 ?_)
        intro p hp
        have hpUE : p ∈ U ∪ E := Or.inl hp
        rw [← himg] at hpUE
        rcases hpUE with hq | hq
        · exact hq
        · exact absurd (h2 hq) (Set.disjoint_left.1 hUE hp)
    · rcases h2or with h2 | h2
      · refine Or.inr (Subset.antisymm h1 ?_)
        intro p hp
        have hpUE : p ∈ U ∪ E := Or.inr hp
        rw [← himg] at hpUE
        rcases hpUE with hq | hq
        · exact hq
        · exact absurd (h2 hq) (Set.disjoint_right.1 hUE hp)
      · exfalso
        obtain ⟨p, hp⟩ := hUne
        have : p ∈ E := by
          have hpUE : p ∈ U ∪ E := Or.inl hp
          rw [← himg] at hpUE
          rcases hpUE with hq | hq
          · exact h1 hq
          · exact h2 hq
        exact (Set.disjoint_left.1 hUE hp) this
  refine LocallyConnectedAt.of_image_homeomorph F ?_
  rcases hmain with h | h
  · rw [h]; exact locallyConnectedAt_openSquare (F z)
  · rw [h]; exact locallyConnectedAt_compl_closedSquare hFz

end AVD
