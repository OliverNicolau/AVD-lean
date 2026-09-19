import AbstractVoronoi.Jordan.Arcs

/-!
# An adapter for the Jordan–Schönflies development

The planar topology used in

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

(the Jordan curve theorem, the Jordan–Schönflies theorem, the non-planarity of `K₃,₃`, arcs
inside open connected sets) is taken from the Lean 4 formalization of the Jordan–Schönflies
theorem,

* Á. Begué, *The Jordan–Schönflies theorem in Lean*,
  <https://github.com/alonamaloh/schoenflies-lean>,

which is a dependency of this project.  That development works with the same plane
`EuclideanSpace ℝ (Fin 2)` as this one, and with notions of simple arc
(`Schoenflies.IsArc`, `Schoenflies.IsArcBetween`) and of Jordan curve
(`Schoenflies.IsJordanCurve`) that are *set*-level readings of the parametrized notions used
here — `AVD.IsArc` and `AVD.IsClosedJordanCurve`, which are stated for parametrizations
`ℝ → ℝ²` continuous on `[0,1]`.  This file relates the two, so that the results of that
development can be used directly in the formalization of the paper.
-/

noncomputable section

open Set Topology

namespace AVD

/-! ## Clamping the parameter

The two developments differ in that ours parametrizes arcs by functions that are only
continuous on `[0,1]`, while the Jordan curve theorem development uses globally continuous
functions.  Composing with the retraction `clamp01` of the line onto `[0,1]` translates
between the two. -/

/-- The retraction of the line onto `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

/-- The retraction `clamp01` of the line onto `[0,1]` is continuous. -/
theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

/-- `clamp01` takes its values in `[0,1]`. -/
theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_left _ _)

/-- `clamp01` is the identity on `[0,1]`. -/
theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  simp [clamp01, ht.1, ht.2]

/-- A parametrization of a subarc of an arc, defined on the whole line: it traverses
`γ` from `γ a` to `γ b` as the parameter runs through `[0,1]`, and is constant outside. -/
def subarcParam (γ : ℝ → Plane) (a b : ℝ) : ℝ → Plane :=
  fun t => γ (a + (b - a) * clamp01 t)

/-- The parameter used by `subarcParam γ a b` stays in `[0,1]` when `[a,b] ⊆ [0,1]`. -/
theorem subarcParam_mem_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (t : ℝ) :
    a + (b - a) * clamp01 t ∈ Icc (0 : ℝ) 1 := by
  have h := clamp01_mem t
  constructor
  · nlinarith [h.1, h.2]
  · nlinarith [h.1, h.2]

/-- A subarc of an arc is parametrized by a globally continuous map. -/
theorem continuous_subarcParam {γ : ℝ → Plane} (h : IsArc γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : Continuous (subarcParam γ a b) := by
  refine h.cont.comp_continuous (by unfold clamp01; fun_prop) ?_
  intro t; exact subarcParam_mem_Icc ha hab hb t

/-- The image of `[0,1]` under `subarcParam γ a b` is the piece `γ([a,b])` of the arc. -/
theorem subarcParam_image {γ : ℝ → Plane} {a b : ℝ} (hab : a ≤ b) :
    subarcParam γ a b '' Icc 0 1 = γ '' Icc a b := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hc := clamp01_mem s
    exact ⟨a + (b - a) * clamp01 s, ⟨by nlinarith [hc.1, hc.2], by nlinarith [hc.1, hc.2]⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le hab with rfl | hab'
    · refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
      have hua : u = a := le_antisymm hu.2 hu.1
      simp [subarcParam, hua]
    · have hne : 0 < b - a := by linarith
      have hmem : (u - a) / (b - a) ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (by linarith [hu.1]) hne.le, by rw [div_le_one hne]; linarith [hu.2]⟩
      refine ⟨(u - a) / (b - a), hmem, ?_⟩
      change γ (a + (b - a) * clamp01 ((u - a) / (b - a))) = γ u
      rw [clamp01_of_mem hmem]
      congr 1
      field_simp
      ring

/-- `subarcParam γ a b` is injective on `[0,1]` when `γ` is an arc and `a < b`. -/
theorem subarcParam_injOn {γ : ℝ → Plane} (h : IsArc γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : InjOn (subarcParam γ a b) (Icc 0 1) := by
  intro s hs t ht hst
  have hpar := h.inj (subarcParam_mem_Icc ha hab.le hb s)
    (subarcParam_mem_Icc ha hab.le hb t) hst
  rw [clamp01_of_mem hs, clamp01_of_mem ht] at hpar
  have hne : b - a ≠ 0 := by linarith
  exact mul_left_cancel₀ hne (by linarith)

/-- A subarc of an arc is an arc between its endpoints, in the sense of the
Jordan–Schönflies development. -/
theorem IsArc.isArcBetween_image {γ : ℝ → Plane} (h : IsArc γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Schoenflies.IsArcBetween (γ '' Icc a b) (γ a) (γ b) := by
  refine ⟨subarcParam γ a b, (continuous_subarcParam h ha hab.le hb).continuousOn,
    subarcParam_injOn h ha hab hb, subarcParam_image hab.le, ?_, ?_⟩
  · change γ (a + (b - a) * clamp01 0) = γ a
    rw [clamp01_of_mem ⟨le_refl 0, zero_le_one⟩]
    congr 1
    ring
  · change γ (a + (b - a) * clamp01 1) = γ b
    rw [clamp01_of_mem ⟨zero_le_one, le_refl 1⟩]
    congr 1
    ring

/-- An arc is an arc between its endpoints, in the sense of the Jordan–Schönflies
development. -/
theorem IsArc.isArcBetween {γ : ℝ → Plane} (h : IsArc γ) :
    Schoenflies.IsArcBetween (γ '' Icc 0 1) (γ 0) (γ 1) :=
  ⟨γ, h.cont, h.inj, rfl, rfl, rfl⟩

/-- An arc is a simple arc in the sense of the Jordan–Schönflies development. -/
theorem IsArc.isArc_image {γ : ℝ → Plane} (h : IsArc γ) :
    Schoenflies.IsArc (γ '' Icc 0 1) :=
  ⟨γ, h.cont, h.inj, rfl⟩

/-- Conversely, an arc between two points in the sense of the Jordan–Schönflies development
is the image of an arc in the sense used here. -/
theorem exists_isArc_of_isArcBetween {C : Set Plane} {x y : Plane}
    (h : Schoenflies.IsArcBetween C x y) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = y ∧ γ '' Icc 0 1 = C := by
  obtain ⟨f, hcont, hinj, hC, h0, h1⟩ := h
  exact ⟨f, ⟨hcont, hinj⟩, h0, h1, hC⟩

/-! ## Closed Jordan curves -/

/-- The notion of closed Jordan curve used here coincides with the notion of Jordan curve of
the Jordan–Schönflies development: both are the image of `[0,1]` under a map that is
continuous there, injective on `[0,1)` and takes the same value at `0` and `1`. -/
theorem isClosedJordanCurve_iff {C : Set Plane} :
    IsClosedJordanCurve C ↔ Schoenflies.IsJordanCurve C := by
  constructor
  · rintro ⟨γ, hcont, hinj, hcl, himg⟩
    exact ⟨γ, ⟨hcont, hcl, hinj⟩, himg⟩
  · rintro ⟨f, ⟨hcont, hcl, hinj⟩, himg⟩
    exact ⟨f, hcont, hinj, hcl, himg⟩

/-- **The Jordan curve theorem**, in the form proved in the Jordan–Schönflies development
and restated for the notion of closed Jordan curve used here: a closed Jordan curve of the
plane splits the plane into two disjoint open connected domains. -/
theorem IsClosedJordanCurve.exists_separation {C : Set Plane} (h : IsClosedJordanCurve C) :
    ∃ A B : Set Plane, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = univ := by
  have hsep := Schoenflies.jordan_curve_theorem (isClosedJordanCurve_iff.1 h)
  refine ⟨Schoenflies.inside C, Schoenflies.outside C, hsep.isOpen_inside, hsep.isOpen_outside,
    hsep.isConnected_inside, hsep.isConnected_outside, Schoenflies.disjoint_inside_outside,
    ?_, ?_, ?_⟩
  · exact Set.disjoint_left.2 fun x hx => Schoenflies.inside_subset_compl hx
  · exact Set.disjoint_left.2 fun x hx => Schoenflies.outside_subset_compl hx
  · rw [Schoenflies.inside_union_outside]
    exact compl_union_self C

/-! ## Arcs inside an open connected set -/

/-- Two distinct points of an open connected subset of the plane are joined by an arc
inside it.  (This is the plane instance of the classical fact, quoted in footnote 5 of
Klein–Langetepe–Nilforoushan (2009), that a connected open set is arcwise connected; it
comes from `Schoenflies.exists_simple_arc_of_isPreconnected`.) -/
theorem exists_arc_in_open {R : Set Plane} (hopen : IsOpen R) (hconn : IsPreconnected R)
    {x y : Plane} (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = y ∧ γ '' Icc 0 1 ⊆ R := by
  obtain ⟨A, hAR, -, harc⟩ :=
    Schoenflies.exists_simple_arc_of_isPreconnected hopen hconn hx hy hxy
  obtain ⟨γ, hγ, h0, h1, himg⟩ := exists_isArc_of_isArcBetween harc
  exact ⟨γ, hγ, h0, h1, himg ▸ hAR⟩

/-! ## Consequences of the Jordan curve theorem

The parts of Theorem 4 of Klein–Langetepe–Nilforoushan (2009) that follow from the Jordan
curve theorem alone: besides the separation into two domains, the fact that the boundary of
each domain is contained in the curve, and that exactly one of the two domains is bounded
(for a *closed* Jordan curve, whose image is compact). -/

/-- The plane has rank greater than one. -/
theorem one_lt_rank_plane : (1 : Cardinal) < Module.rank ℝ Plane := by
  have h : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  rw [← Module.finrank_eq_rank ℝ Plane, h]
  norm_num

/-- The complement of a closed ball of the plane is connected. -/
theorem isConnected_compl_closedBall {r : ℝ} (hr : 0 < r) :
    IsConnected ((Metric.closedBall (0 : Plane) r)ᶜ) := by
  have hsphere : IsConnected (Metric.sphere (0 : Plane) 1) :=
    isConnected_sphere one_lt_rank_plane 0 zero_le_one
  have hprod : IsConnected (Ioi r ×ˢ Metric.sphere (0 : Plane) 1) :=
    (isConnected_Ioi).prod hsphere
  have himg := hprod.image (fun p : ℝ × Plane => p.1 • p.2) (by fun_prop)
  convert himg using 1
  ext y
  simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, mem_image,
    Set.mem_prod, mem_Ioi, Metric.mem_sphere, Prod.exists]
  constructor
  · intro hy
    have hy0 : ‖y‖ ≠ 0 := ne_of_gt (hr.trans hy)
    refine ⟨‖y‖, ‖y‖⁻¹ • y, ⟨hy, ?_⟩, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hy0]
    · rw [smul_smul, mul_inv_cancel₀ hy0, one_smul]
  · rintro ⟨a, x, ⟨ha, hx⟩, rfl⟩
    rw [norm_smul, hx, mul_one, Real.norm_eq_abs, abs_of_pos (lt_trans hr ha)]
    exact ha

/-- The complement of a closed ball of the plane is unbounded. -/
theorem not_isBounded_compl_closedBall {r : ℝ} :
    ¬ Bornology.IsBounded ((Metric.closedBall (0 : Plane) r)ᶜ) := by
  intro hbdd
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbdd
  set c : ℝ := |R| + |r| + 1 with hc
  set y : Plane := EuclideanSpace.single 0 c with hy
  have hnorm : ‖y‖ = c := by
    rw [hy, PiLp.norm_single 2 (fun _ => ℝ) 0 c]
    exact abs_of_pos (by positivity)
  have hmem : y ∈ (Metric.closedBall (0 : Plane) r)ᶜ := by
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le, hnorm, hc]
    have := le_abs_self r
    linarith [abs_nonneg R]
  have := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right, hnorm, hc] at this
  have := le_abs_self R
  linarith [abs_nonneg r]

/-- A closed Jordan curve is compact. -/
theorem IsClosedJordanCurve.isCompact {C : Set Plane} (h : IsClosedJordanCurve C) :
    IsCompact C := by
  obtain ⟨γ, hcont, -, -, himg⟩ := h
  rw [← himg]
  exact isCompact_Icc.image_of_continuousOn hcont

/-- **The Jordan curve theorem, in the form used in Theorem 4** of
Klein–Langetepe–Nilforoushan (2009), as far as it follows from the Jordan curve theorem
itself: a closed Jordan curve `C` splits the plane into two disjoint domains `D₁`, `D₂`
whose union is `ℝ² \ C`, the boundary of each of which is contained in `C`, and exactly one
of which is bounded.

(The remaining assertions of Theorem 4 — that the boundary of each domain is *all* of `C`,
and the local accessibility of the points of `C` — belong to the Jordan–Schönflies theorem
and are not covered by this.) -/
theorem IsClosedJordanCurve.exists_separation_frontier {C : Set Plane}
    (h : IsClosedJordanCurve C) :
    ∃ D₁ D₂ : Set Plane, IsOpen D₁ ∧ IsOpen D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧
      Disjoint D₁ D₂ ∧ D₁ ∪ D₂ = Cᶜ ∧ frontier D₁ ⊆ C ∧ frontier D₂ ⊆ C ∧
      ((Bornology.IsBounded D₁ ∧ ¬ Bornology.IsBounded D₂) ∨
        (Bornology.IsBounded D₂ ∧ ¬ Bornology.IsBounded D₁)) := by
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAC, hBC, hcover⟩ := h.exists_separation
  have hunion : A ∪ B = Cᶜ := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact fun hxC => (Set.disjoint_left.1 hAC) hx hxC
      · exact fun hxC => (Set.disjoint_left.1 hBC) hx hxC
    · intro x hx
      have : x ∈ A ∪ B ∪ C := by rw [hcover]; trivial
      rcases this with h' | h'
      · exact h'
      · exact absurd h' hx
  -- the boundary of each domain is contained in the curve
  have hfront : ∀ U V : Set Plane, IsOpen U → IsOpen V → Disjoint U V → U ∪ V = Cᶜ →
      frontier U ⊆ C := by
    intro U V hU hV hUV hcov x hx
    by_contra hxC
    have hxUV : x ∈ U ∪ V := by rw [hcov]; exact hxC
    have hxnotU : x ∉ U := by
      have h2 := hx.2
      rwa [hU.interior_eq] at h2
    rcases hxUV with hxU | hxV
    · exact hxnotU hxU
    · exact (Set.disjoint_left.1 (hUV.symm.closure_right hV)) hxV hx.1
  -- exactly one of the two domains is bounded
  have hCbdd : Bornology.IsBounded C := h.isCompact.isBounded
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hCbdd
  have hrpos : 0 < |r| + 1 := by positivity
  have hsub : (Metric.closedBall (0 : Plane) (|r| + 1))ᶜ ⊆ A ∪ B := by
    rw [hunion]
    intro x hx hxC
    have := hr hxC
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_abs_self r]
  have hconn := (isConnected_compl_closedBall hrpos).isPreconnected
  have hchoice := hconn.subset_or_subset hAo hBo hAB hsub
  have hbdd_of_sub : ∀ U V : Set Plane, U ∪ V = Cᶜ → Disjoint U V →
      (Metric.closedBall (0 : Plane) (|r| + 1))ᶜ ⊆ U → Bornology.IsBounded V := by
    intro U V hcov hdisj hUsub
    have : V ⊆ Metric.closedBall (0 : Plane) (|r| + 1) := by
      intro x hx
      by_contra hxb
      exact (Set.disjoint_left.1 hdisj) (hUsub hxb) hx
    exact Bornology.IsBounded.subset (Metric.isBounded_closedBall) this
  rcases hchoice with hA | hB
  · refine ⟨A, B, hAo, hBo, hAc, hBc, hAB, hunion, hfront A B hAo hBo hAB hunion,
      hfront B A hBo hAo hAB.symm (by rw [Set.union_comm]; exact hunion), Or.inr ⟨?_, ?_⟩⟩
    · exact hbdd_of_sub A B hunion hAB hA
    · intro hbdd
      exact not_isBounded_compl_closedBall (hbdd.subset hA)
  · refine ⟨A, B, hAo, hBo, hAc, hBc, hAB, hunion, hfront A B hAo hBo hAB hunion,
      hfront B A hBo hAo hAB.symm (by rw [Set.union_comm]; exact hunion), Or.inl ⟨?_, ?_⟩⟩
    · exact hbdd_of_sub B A (by rw [Set.union_comm]; exact hunion) hAB.symm hB
    · intro hbdd
      exact not_isBounded_compl_closedBall (hbdd.subset hB)

end AVD
