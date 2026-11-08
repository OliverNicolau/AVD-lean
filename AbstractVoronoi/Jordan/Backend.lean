import AbstractVoronoi.Jordan.SupNorm
import TauCeti.Topology.JordanCurve.Interval
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve

/-!
# The planar-topology backend

This file is the **only** place where the development uses an external formalization of
planar topology.  It states, for the plane `EuclideanSpace ℝ (Fin 2)`, the results that the
rest of the project takes from outside, and proves them from

* Tau Ceti, <https://github.com/TauCetiProject/TauCeti>, commit
  `4908b0344e1be5f7e9e5af7f7e640464843a2c84` (Apache License 2.0),

together with Mathlib.  The Tau Ceti source files used are

* `TauCeti/Topology/JordanCurve/Basic.lean` (Jordan curves as homeomorphic copies of the circle:
  `TauCeti.isJordanCurve_iff`, `TauCeti.IsJordanCurve.image_homeomorph`,
  `TauCeti.isJordanCurve_image_homeomorph_iff`, `TauCeti.isJordanCurve_sphere`).
* `TauCeti/Topology/JordanCurve/Interval.lean` (`TauCeti.isJordanCurve_iff_exists_injOn_Ico`,
  the bridge to the parametrized definition below).
* `TauCeti/Analysis/Complex/Conformal/Jordan/Schoenflies.lean` (the Jordan–Schönflies theorem
  in `ℂ`, `TauCeti.IsJordanCurve.exists_homeomorph_image_sphere`).
* `TauCeti/Analysis/Normed/Module/Ball/Radial/Cone.lean` (the cone over a homeomorphism of unit
  spheres, `Homeomorph.sphereCone`).
* `TauCeti/Analysis/Complex/PlaneSeparation/JordanCurve.lean` (a simple arc does not separate
  the plane, `Path.isConnected_compl_range_of_injective`).

The plane `ℂ` of Tau Ceti is identified with `EuclideanSpace ℝ (Fin 2)` by the linear isometry
`Complex.orthonormalBasisOneI.repr`.  From Mathlib the file also uses
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` (a bounded convex body is
homeomorphic to the closed unit ball) and `isConnected_compl_singleton_of_one_lt_rank`.

Every other file reaches these developments only through the declarations below, so this
file is the trust boundary of the project, and replacing the backend means re-proving
exactly these statements.

## Statements

* `Backend.IsArc`, `Backend.IsArcBetween`, `Backend.IsJordanCurve`: set-level simple arcs
  and Jordan curves (images of `[0,1]`).
* `Backend.jordan_curve_theorem`: a Jordan curve splits the plane into two disjoint
  connected open domains.
* `Backend.isConnected_compl_arc`: the complement of a simple arc is connected.
* `Backend.jordan_schoenflies_of_homeomorph`: a homeomorphism between two Jordan curves
  extends to a homeomorphism of the plane.
* `Backend.isJordanCurve_modelCurve`, `Backend.IsJordanCurve.nonempty_homeomorph_modelCurve`:
  the boundary of the square `[-1,1]²` is a Jordan curve, homeomorphic to every Jordan curve.
-/

noncomputable section

open Set Metric

namespace AVD

namespace Backend

/-- The plane, written out (this file sits below `AbstractVoronoi/Jordan/Sphere.lean`, where
the abbreviation `AVD.Plane` is introduced; the two are the same type). -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Definitions -/

/-- A simple arc: the image of `[0,1]` under a map continuous and injective there. -/
def IsArc (A : Set ℝ²) : Prop :=
  ∃ f : ℝ → ℝ², ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f '' Icc 0 1 = A

/-- A simple arc from `p` to `q`. -/
def IsArcBetween (A : Set ℝ²) (p q : ℝ²) : Prop :=
  ∃ f : ℝ → ℝ², ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f '' Icc 0 1 = A ∧
    f 0 = p ∧ f 1 = q

/-- A Jordan curve: the image of `[0,1]` under a map continuous there, injective on `[0,1)`,
taking the same value at `0` and `1`. -/
def IsJordanCurve (C : Set ℝ²) : Prop :=
  ∃ f : ℝ → ℝ², ContinuousOn f (Icc 0 1) ∧ f 0 = f 1 ∧ InjOn f (Ico 0 1) ∧
    f '' Icc 0 1 = C

/-! ## Bridges to Tau Ceti -/

/-- Backend's Jordan curves are Tau Ceti's (`TauCeti.isJordanCurve_iff_exists_injOn_Ico` at
`[0,1]`; the fields come in the same order). -/
theorem isJordanCurve_iff_tauCeti {C : Set ℝ²} :
    IsJordanCurve C ↔ TauCeti.IsJordanCurve C :=
  (TauCeti.isJordanCurve_iff_exists_injOn_Ico zero_lt_one).symm

/-- The identification of `ℂ` with the plane, by the orthonormal basis `1, i`. -/
private abbrev Φ : ℂ ≃ₜ ℝ² := Complex.orthonormalBasisOneI.repr.toHomeomorph

/-- Schoenflies in the plane: a Jordan curve is the image of the unit circle of `ℂ` under a
homeomorphism `ℂ ≃ₜ ℝ²`. -/
private theorem exists_homeomorph_image_sphere {C : Set ℝ²} (hC : IsJordanCurve C) :
    ∃ g : ℂ ≃ₜ ℝ², g '' sphere 0 1 = C := by
  have h : TauCeti.IsJordanCurve (Φ.symm '' C) :=
    (isJordanCurve_iff_tauCeti.1 hC).image_homeomorph Φ.symm
  obtain ⟨e, he, -, -⟩ := h.exists_homeomorph_image_sphere
  refine ⟨e.trans Φ, ?_⟩
  change (Φ ∘ e) '' _ = C
  rw [image_comp, he, ← image_comp]
  simp

/-- The outside of the closed unit disc of `ℂ` is connected: it is the image of `ℂ \ {0}` under
`z ↦ z + z / ‖z‖`. -/
private theorem isConnected_compl_closedBall_complex :
    IsConnected (closedBall (0 : ℂ) 1)ᶜ := by
  have h1 : IsConnected ({0}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have himg : (fun z : ℂ => z + (‖z‖⁻¹ : ℂ) * z) '' {0}ᶜ = (closedBall (0 : ℂ) 1)ᶜ := by
    ext w
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, mem_closedBall, dist_zero_right,
      not_le]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have : z + (‖z‖⁻¹ : ℂ) * z = ((1 + ‖z‖⁻¹ : ℝ) : ℂ) * z := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), add_mul,
        inv_mul_cancel₀ hn.ne']
      linarith
    · intro hw
      have hn : 0 < ‖w‖ := by linarith
      refine ⟨((1 - ‖w‖⁻¹ : ℝ) : ℂ) * w, ?_, ?_⟩
      · have : (1 - ‖w‖⁻¹ : ℝ) ≠ 0 := by
          have : ‖w‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hw
          linarith
        exact mul_ne_zero (by exact_mod_cast this) (norm_pos_iff.1 hn)
      · have hpos : 0 < 1 - ‖w‖⁻¹ := by have := inv_lt_one_of_one_lt₀ hw; linarith
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le, sub_mul,
          inv_mul_cancel₀ hn.ne', one_mul]
        have key : ((1 - ‖w‖⁻¹ + (‖w‖ - 1)⁻¹ * (1 - ‖w‖⁻¹) : ℝ) : ℂ) = 1 := by
          have h1 : ‖w‖ - 1 ≠ 0 := by linarith
          have : (1 - ‖w‖⁻¹ + (‖w‖ - 1)⁻¹ * (1 - ‖w‖⁻¹) : ℝ) = 1 := by
            field_simp
            ring
          rw [this]; simp
        push_cast at key ⊢
        linear_combination w * key
  rw [← himg]
  refine h1.image _ (ContinuousOn.add continuousOn_id (ContinuousOn.mul ?_ continuousOn_id))
  exact (Complex.continuous_ofReal.comp continuous_norm).continuousOn.inv₀
    fun z hz => by simpa using hz

open Square in
private theorem supNorm_smul {t : ℝ} (ht : 0 ≤ t) (x : ℝ²) : supNorm (t • x) = t * supNorm x := by
  simp [supNorm, abs_mul, abs_of_nonneg ht, mul_max_of_nonneg _ _ ht]

open Square in
/-- The model curve is the frontier of the closed square `[-1,1]²`. -/
theorem modelCurve_eq_frontier : modelCurve = frontier (closedSquare 0 1) := by
  rw [closedSquare_zero]
  refine Subset.antisymm (fun x hx => ?_)
    (frontier_le_subset_eq continuous_supNorm continuous_const)
  have hx : supNorm x = 1 := hx
  have hcl : IsClosed {x : ℝ² | supNorm x ≤ 1} := isClosed_le continuous_supNorm continuous_const
  rw [frontier, hcl.closure_eq]
  refine ⟨hx.le, fun hint => ?_⟩
  -- points `t • x` with `t > 1` lie outside the closed square and tend to `x`
  have hlim : Filter.Tendsto (fun t : ℝ => t • x) (nhdsWithin 1 (Ioi 1)) (nhds x) := by
    have : Filter.Tendsto (fun t : ℝ => t • x) (nhds 1) (nhds ((1 : ℝ) • x)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, ht1⟩ := ((hlim.eventually (isOpen_interior.mem_nhds hint)).and
    self_mem_nhdsWithin).exists
  have := interior_subset ht
  simp only [mem_ofPred_eq, supNorm_smul (zero_le_one.trans (le_of_lt ht1)), hx, mul_one] at this
  exact absurd this (not_le.2 ht1)

/-! ## The statements -/

/-- **The Jordan curve theorem.**  The complement of a Jordan curve is the union of two
disjoint connected open sets. -/
theorem jordan_curve_theorem {C : Set ℝ²} (hC : IsJordanCurve C) :
    ∃ A B : Set ℝ², IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = univ := by
  obtain ⟨g, hg⟩ := exists_homeomorph_image_sphere hC
  subst hg
  have hdisj : ∀ {s t : Set ℂ}, Disjoint s t → Disjoint (g '' s) (g '' t) := fun h =>
    (disjoint_image_iff g.injective).2 h
  refine ⟨g '' ball 0 1, g '' (closedBall 0 1)ᶜ, g.isOpenMap _ isOpen_ball,
    g.isOpenMap _ isClosed_closedBall.isOpen_compl,
    (isConnected_ball one_pos).image _ g.continuous.continuousOn,
    isConnected_compl_closedBall_complex.image _ g.continuous.continuousOn,
    hdisj (disjoint_compl_right.mono_left ball_subset_closedBall),
    hdisj ?_, hdisj ?_, ?_⟩
  · exact Set.disjoint_left.2 fun z hz hz' => (mem_ball.1 hz).ne (mem_sphere.1 hz')
  · exact disjoint_compl_left.mono_right sphere_subset_closedBall
  · rw [← image_union, ← image_union, ← image_univ_of_surjective g.surjective]
    congr 1
    ext z
    simp only [mem_union, mem_ball, mem_compl_iff, mem_closedBall, mem_sphere, not_le, mem_univ,
      iff_true]
    rcases lt_trichotomy (dist z 0) 1 with h | h | h
    exacts [Or.inl (Or.inl h), Or.inr h, Or.inl (Or.inr h)]

/-- **A simple arc does not separate the plane**: its complement is connected. -/
theorem isConnected_compl_arc {A : Set ℝ²} (hA : IsArc A) : IsConnected Aᶜ := by
  obtain ⟨γ, hcont, hinj, rfl⟩ := hA
  set e := Complex.orthonormalBasisOneI.repr
  let P : Path (e.symm (γ 0)) (e.symm (γ 1)) :=
    { toFun := fun t => e.symm (γ t)
      continuous_toFun := e.symm.continuous.comp hcont.domRestrict
      source' := rfl
      target' := rfl }
  have hinjP : Function.Injective P := fun s t hst =>
    Subtype.ext (hinj s.2 t.2 (e.symm.injective hst))
  have hrange : range P = e.symm '' (γ '' Icc 0 1) := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨γ t, ⟨t, t.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hconn := P.isConnected_compl_range_of_injective hinjP
  rw [hrange] at hconn
  have hpre : (γ '' Icc 0 1)ᶜ = e.symm ⁻¹' (e.symm '' (γ '' Icc 0 1))ᶜ := by
    rw [preimage_compl, e.symm.injective.preimage_image]
  rw [hpre]
  exact (e.symm.toHomeomorph.isConnected_preimage).2 hconn

/-- **The Jordan–Schönflies theorem.**  Every homeomorphism between two Jordan curves extends
to a homeomorphism of the plane. -/
theorem jordan_schoenflies_of_homeomorph {C C' : Set ℝ²} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (e : C ≃ₜ C') : ∃ F : ℝ² ≃ₜ ℝ², ∀ z : C, F z = e z := by
  obtain ⟨g₁, h₁⟩ := exists_homeomorph_image_sphere hC
  obtain ⟨g₂, h₂⟩ := exists_homeomorph_image_sphere hC'
  let σ : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : ℂ) 1 :=
    ((((g₁.image _).trans (Homeomorph.setCongr h₁)).trans e).trans
      (Homeomorph.setCongr h₂.symm)).trans (g₂.image _).symm
  refine ⟨(g₁.symm.trans σ.sphereCone).trans g₂, fun z => ?_⟩
  have hz : g₁.symm z ∈ sphere (0 : ℂ) 1 := by
    obtain ⟨u, hu, hzu⟩ : (z : ℝ²) ∈ g₁ '' sphere 0 1 := h₁ ▸ z.2
    rw [← hzu, Homeomorph.symm_apply_apply]
    exact hu
  have := σ.sphereCone_apply_coe ⟨_, hz⟩
  simp only at this
  simp [this, σ]

open Square in
/-- The model curve, the boundary of the square `[-1,1]²`, is a Jordan curve. -/
theorem isJordanCurve_modelCurve : IsJordanCurve Square.modelCurve := by
  have hconv : Convex ℝ (closedSquare (0 : ℝ²) 1) := by
    rw [closedSquare_zero]; simpa using convexOn_supNorm.convex_le 1
  have hint : (interior (closedSquare (0 : ℝ²) 1)).Nonempty := by
    refine ⟨0, interior_maximal (fun x hx => ?_) (isOpen_openSquare 1) ?_⟩
    · rw [openSquare_zero] at hx
      rw [closedSquare_zero]
      exact le_of_lt (show supNorm x < 1 from hx)
    · rw [openSquare_zero]; simp [supNorm]
  have hbdd : Bornology.IsBounded (closedSquare (0 : ℝ²) 1) := by
    refine (isBounded_closedBall (x := (0 : ℝ²)) (r := Real.sqrt 2)).subset fun x hx => ?_
    rw [closedSquare_zero] at hx
    rw [mem_closedBall, dist_zero_right]
    calc ‖x‖ ≤ Real.sqrt 2 * supNorm x := norm_le_sqrt_two_mul_supNorm x
      _ ≤ Real.sqrt 2 * 1 := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 := mul_one _
  obtain ⟨h, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hint hbdd
  rw [isJordanCurve_iff_tauCeti, modelCurve_eq_frontier,
    ← TauCeti.isJordanCurve_image_homeomorph_iff h, hfr]
  have : sphere (0 : ℝ²) 1 = Φ '' sphere (0 : ℂ) 1 := by
    simp [Φ, LinearIsometryEquiv.image_sphere]
  rw [this]
  exact (TauCeti.isJordanCurve_sphere 0 one_pos).image_homeomorph Φ

/-- Every Jordan curve is homeomorphic to the model curve. -/
theorem IsJordanCurve.nonempty_homeomorph_modelCurve {C : Set ℝ²} (hC : IsJordanCurve C) :
    Nonempty (C ≃ₜ Square.modelCurve) := by
  obtain ⟨e₁⟩ := TauCeti.isJordanCurve_iff.1 (isJordanCurve_iff_tauCeti.1 hC)
  obtain ⟨e₂⟩ := TauCeti.isJordanCurve_iff.1 (isJordanCurve_iff_tauCeti.1 isJordanCurve_modelCurve)
  exact ⟨e₁.trans e₂.symm⟩

end Backend

end AVD
