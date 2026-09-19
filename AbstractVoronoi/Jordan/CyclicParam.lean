import AbstractVoronoi.Jordan.Sphere

/-!
# Cyclic parametrizations of closed Jordan curves

A closed Jordan curve in the sense of `AVD.IsClosedJordanCurve` is presented by a
parametrization `γ : [0,1] → X` with `γ 0 = γ 1` which is injective on `[0,1)`.  For the
arguments of **Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

it is far more convenient to have the parametrization available on the whole line, as a
`1`-periodic map `Γ : ℝ → X` which is injective modulo `1`.  This file provides such
*cyclic parametrizations* and the basic surgery on them: every sub-interval of length
`< 1` is mapped onto an arc, and the complement in the curve of the (open) image of a short
interval is the image of the complementary closed interval.

This is the tool used in `AbstractVoronoi.Jordan.Schoenflies` to run the classical "theta curve"
argument showing that the boundary of each complementary domain of a closed Jordan curve is
the *whole* curve, which is one of the assertions of Theorem 4 of the paper.
-/

noncomputable section

open Set Topology

namespace AVD

local instance : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- A *cyclic parametrization* of a set `C`: a continuous `1`-periodic map `ℝ → X` with
image `C` which is injective modulo `1`.  This is the closed curve of
`AVD.IsClosedJordanCurve`, parametrized on the whole line instead of on `[0,1]`. -/
structure IsCyclicParam {X : Type*} [TopologicalSpace X] (Γ : ℝ → X) (C : Set X) : Prop where
  cont : Continuous Γ
  per : ∀ t, Γ (t + 1) = Γ t
  inj : ∀ ⦃a b : ℝ⦄, Γ a = Γ b → ∃ n : ℤ, b - a = n
  range_eq : range Γ = C

namespace IsCyclicParam

variable {X : Type*} [TopologicalSpace X] {Γ : ℝ → X} {C : Set X}

/-- A cyclic parametrization is invariant under integer translations of the parameter. -/
theorem per_int (h : IsCyclicParam Γ C) (t : ℝ) (n : ℤ) : Γ (t + n) = Γ t := by
  have hp : Function.Periodic Γ 1 := h.per
  simpa using hp.int_mul n t

/-- A cyclic parametrization is injective on every interval of length `< 1`. -/
theorem injOn (h : IsCyclicParam Γ C) {a b : ℝ} (hab : b - a < 1) : InjOn Γ (Icc a b) := by
  intro s hs t ht hst
  obtain ⟨n, hn⟩ := h.inj hst
  have h1 : |(n : ℝ)| < 1 := by
    rw [← hn, abs_lt]
    constructor <;> [linarith [hs.1, hs.2, ht.1, ht.2]; linarith [hs.1, hs.2, ht.1, ht.2]]
  have : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    linarith
  simp [this] at hn
  linarith

/-- The image of any closed interval of length `1` is the whole curve. -/
theorem image_Icc (h : IsCyclicParam Γ C) (a : ℝ) : Γ '' Icc a (a + 1) = C := by
  apply Subset.antisymm
  · rintro x ⟨t, -, rfl⟩
    rw [← h.range_eq]; exact mem_range_self t
  · rw [← h.range_eq]
    rintro x ⟨t, rfl⟩
    refine ⟨a + Int.fract ((t - a) / 1), ⟨by simp [Int.fract_nonneg], ?_⟩, ?_⟩
    · have := Int.fract_lt_one ((t - a) / 1)
      linarith
    · have hfr : Int.fract (t - a) = (t - a) - ⌊t - a⌋ := rfl
      simp only [div_one, hfr]
      have : a + (t - a - (⌊t - a⌋ : ℝ)) = t + (-⌊t - a⌋ : ℤ) := by push_cast; ring
      rw [this, h.per_int]

/-- The union of the images of the two complementary intervals `[a, b]` and `[b, a+1]` is
the whole curve. -/
theorem image_union (h : IsCyclicParam Γ C) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 1) :
    Γ '' Icc a b ∪ Γ '' Icc b (a + 1) = C := by
  rw [← Set.image_union, Icc_union_Icc_eq_Icc hab hb, h.image_Icc]

/-- Every piece of the curve cut out by a parameter interval of length `< 1` is an arc: it
carries a parametrization by `[0,1]` which is continuous and injective. -/
theorem exists_param_Icc (h : IsCyclicParam Γ C) {a b : ℝ} (hab : a < b) (hlen : b - a < 1) :
    ∃ κ : ℝ → X, Continuous κ ∧ InjOn κ (Icc 0 1) ∧ κ 0 = Γ a ∧ κ 1 = Γ b ∧
      κ '' Icc 0 1 = Γ '' Icc a b := by
  have hba : 0 < b - a := by linarith
  refine ⟨fun t => Γ (a + (b - a) * t), h.cont.comp (by fun_prop), ?_, by simp, by ring_nf, ?_⟩
  · intro s hs t ht hst
    have hmem : ∀ x ∈ Icc (0 : ℝ) 1, a + (b - a) * x ∈ Icc a b := by
      intro x hx
      constructor <;> nlinarith [hx.1, hx.2]
    have hkey := h.injOn hlen (hmem s hs) (hmem t ht) hst
    have hne : b - a ≠ 0 := ne_of_gt hba
    exact mul_left_cancel₀ hne (by linarith)
  · apply Subset.antisymm
    · rintro x ⟨s, hs, rfl⟩
      exact ⟨a + (b - a) * s, ⟨by nlinarith [hs.1, hs.2], by nlinarith [hs.1, hs.2]⟩, rfl⟩
    · rintro x ⟨u, hu, rfl⟩
      refine ⟨(u - a) / (b - a), ⟨div_nonneg (by linarith [hu.1]) hba.le,
        by rw [div_le_one hba]; linarith [hu.2]⟩, ?_⟩
      have heq : a + (b - a) * ((u - a) / (b - a)) = u := by field_simp; ring
      change Γ (a + (b - a) * ((u - a) / (b - a))) = Γ u
      rw [heq]

/-- Existence of a cyclic parametrization of a closed Jordan curve. -/
theorem _root_.AVD.IsClosedJordanCurve.exists_cyclicParam {C : Set X}
    (h : IsClosedJordanCurve C) : ∃ Γ : ℝ → X, IsCyclicParam Γ C := by
  obtain ⟨γ, hcont, hinj, hcl, himg⟩ := h
  set F : AddCircle (1 : ℝ) → X := AddCircle.liftIco 1 0 γ with hFdef
  refine ⟨fun t => F (t : AddCircle (1 : ℝ)), ?_, ?_, ?_, ?_⟩
  · have hF : Continuous F :=
      AddCircle.liftIco_continuous (by simpa using hcl) (by simpa using hcont)
    exact hF.comp (by fun_prop)
  · intro t
    have : ((t + 1 : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
      simp
    simp only [this]
  · -- injectivity modulo `1`
    have key : ∀ t : ℝ, F (t : AddCircle (1 : ℝ)) =
        γ ((AddCircle.equivIco (1 : ℝ) 0 (t : AddCircle (1 : ℝ)) : ℝ)) := by
      intro t
      set u : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (t : AddCircle (1 : ℝ)) : ℝ) with hu
      have hmem : u ∈ Ico (0 : ℝ) (0 + 1) :=
        (AddCircle.equivIco (1 : ℝ) 0 (t : AddCircle (1 : ℝ))).2
      have hcoe : ((u : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
        (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _
      rw [← hcoe, hFdef, AddCircle.liftIco_coe_apply hmem]
    intro a b hab
    rw [key a, key b] at hab
    set u : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (a : AddCircle (1 : ℝ)) : ℝ) with hu
    set v : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (b : AddCircle (1 : ℝ)) : ℝ) with hv
    have hu' : u ∈ Ico (0 : ℝ) 1 := by
      have h2 : u ∈ Ico (0 : ℝ) (0 + 1) := (AddCircle.equivIco (1 : ℝ) 0 (a : AddCircle (1 : ℝ))).2
      rwa [zero_add] at h2
    have hv' : v ∈ Ico (0 : ℝ) 1 := by
      have h2 : v ∈ Ico (0 : ℝ) (0 + 1) := (AddCircle.equivIco (1 : ℝ) 0 (b : AddCircle (1 : ℝ))).2
      rwa [zero_add] at h2
    have huv : u = v := hinj hu' hv' hab
    have hca : ((u : ℝ) : AddCircle (1 : ℝ)) = (a : AddCircle (1 : ℝ)) :=
      (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _
    have hcb : ((v : ℝ) : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) :=
      (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _
    have hcoe : ((a : ℝ) : AddCircle (1 : ℝ)) = (b : AddCircle (1 : ℝ)) := by
      rw [← hca, ← hcb, huv]
    -- from equality in the circle, the difference is an integer
    have hmem : (b - a) ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      have := QuotientAddGroup.eq_iff_sub_mem.1 hcoe.symm
      simpa using this
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
    exact ⟨n, by rw [← hn]; simp⟩
  · -- the range is the curve
    apply Subset.antisymm
    · rintro x ⟨t, rfl⟩
      change F ((t : ℝ) : AddCircle (1 : ℝ)) ∈ C
      set u : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ((t : ℝ) : AddCircle (1 : ℝ)) : ℝ) with hu
      have hmem : u ∈ Ico (0 : ℝ) (0 + 1) :=
        (AddCircle.equivIco (1 : ℝ) 0 ((t : ℝ) : AddCircle (1 : ℝ))).2
      have hcoe : ((u : ℝ) : AddCircle (1 : ℝ)) = ((t : ℝ) : AddCircle (1 : ℝ)) :=
        (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply _
      rw [← hcoe, hFdef, AddCircle.liftIco_coe_apply hmem, ← himg]
      exact ⟨u, ⟨hmem.1, by simpa using hmem.2.le⟩, rfl⟩
    · rw [← himg]
      rintro x ⟨s, hs, rfl⟩
      rcases eq_or_lt_of_le hs.2 with h1 | h1
      · refine ⟨0, ?_⟩
        have hmem : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by norm_num
        change F ((0 : ℝ) : AddCircle (1 : ℝ)) = γ s
        rw [hFdef, AddCircle.liftIco_coe_apply hmem, hcl, h1]
      · refine ⟨s, ?_⟩
        have hmem : s ∈ Ico (0 : ℝ) (0 + 1) := ⟨hs.1, by simpa using h1⟩
        change F ((s : ℝ) : AddCircle (1 : ℝ)) = γ s
        rw [hFdef, AddCircle.liftIco_coe_apply hmem]

end IsCyclicParam

end AVD
