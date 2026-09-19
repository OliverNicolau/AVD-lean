import AbstractVoronoi.Paper.Lemma5

/-!
# Three sites: the construction behind Lemma 6

Subsection 3.1 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

This file contains the notions used throughout that subsection — a parametrization of a
bisecting curve through a given point, and the two local branches of such a curve at that
point — together with `AVD.CurveSystem.lemma6_core`, the closed Jordan curve construction
which is the whole content of the proof of Lemma 6.

The numbered statements are elsewhere: **Lemma 6** in `AbstractVoronoi.Paper.Lemma6`,
**Lemma 7** in `AbstractVoronoi.Paper.Lemma7`, **Lemma 8** in `AbstractVoronoi.Paper.Lemma8`.
-/


noncomputable section

open Set Topology

namespace AVD

variable {ι : Type*} [DecidableEq ι]

/-- `IsProperLineParamAt γ C w` : `γ` parametrizes the curve `C` and passes through `w` at time `0`.
This is the situation `g(0) = w` of the discussion preceding Lemma 7 of
Klein–Langetepe–Nilforoushan (2009). -/
def IsProperLineParamAt (γ : ℝ → Plane) (C : Set Plane) (w : Plane) : Prop :=
  IsProperLineParam γ C ∧ γ 0 = w

/-- The branch of the curve `γ` *before* the distinguished point `γ 0` stays inside `A`:
this formalises "`G⁻ := g((-δ,0)) ⊆ A` for some `δ > 0`" of the discussion preceding
Lemma 7 of Klein–Langetepe–Nilforoushan (2009). -/
def BranchBefore (γ : ℝ → Plane) (A : Set Plane) : Prop :=
  ∃ δ > (0 : ℝ), γ '' Ioo (-δ) 0 ⊆ A

/-- The branch of the curve `γ` *after* the distinguished point `γ 0` stays inside `A`:
this formalises "`G⁺ := g((0,δ')) ⊆ A` for some `δ' > 0`" of the discussion preceding
Lemma 7 of Klein–Langetepe–Nilforoushan (2009). -/
def BranchAfter (γ : ℝ → Plane) (A : Set Plane) : Prop :=
  ∃ δ > (0 : ℝ), γ '' Ioo 0 δ ⊆ A

/-- A proper parametrization of a curve is a closed embedding, so a small piece of the curve
around the base point `γ 0` is cut out by a neighbourhood of `γ 0` in the plane. -/
theorem IsProperLineParam.exists_nbhd {γ : ℝ → Plane} {Cu : Set Plane}
    (hγ : IsProperLineParam γ Cu) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : Set Plane, IsOpen W ∧ γ 0 ∈ W ∧ Cu ∩ W ⊆ γ '' Ioo (-δ) δ := by
  obtain ⟨hcont, hinj, hrange, hproper⟩ := hγ
  have hproper' : IsProperMap γ :=
    isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => hproper K hK⟩
  have hclosed : IsClosed (γ '' (Ioo (-δ) δ)ᶜ) :=
    hproper'.isClosedMap _ isOpen_Ioo.isClosed_compl
  refine ⟨(γ '' (Ioo (-δ) δ)ᶜ)ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨c, hc, hc0⟩
    exact hc (by rw [hinj hc0]; exact ⟨by linarith, hδ⟩)
  · rintro x ⟨hxC, hxW⟩
    rw [← hrange] at hxC
    obtain ⟨c, rfl⟩ := hxC
    by_cases hcmem : c ∈ Ioo (-δ) δ
    · exact ⟨c, hcmem, rfl⟩
    · exact absurd ⟨c, hcmem, rfl⟩ hxW

/-- A proper parametrization run backwards is again a proper parametrization of the same
curve. -/
theorem IsProperLineParam.reflect {γ : ℝ → Plane} {Cu : Set Plane}
    (hγ : IsProperLineParam γ Cu) : IsProperLineParam (fun t => γ (-t)) Cu := by
  obtain ⟨hcont, hinj, hrange, hproper⟩ := hγ
  refine ⟨hcont.comp continuous_neg, fun a b hab => ?_, ?_, fun K hK => ?_⟩
  · have := hinj hab
    linarith
  · rw [← hrange]
    apply Subset.antisymm
    · rintro x ⟨t, rfl⟩
      exact ⟨-t, rfl⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨-t, by simp⟩
  · have himg : (fun t => γ (-t)) ⁻¹' K = Neg.neg '' (γ ⁻¹' K) := by
      ext t
      simp only [mem_preimage, mem_image]
      constructor
      · intro h
        exact ⟨-t, h, neg_neg t⟩
      · rintro ⟨s, hs, rfl⟩
        simpa using hs
    rw [himg]
    exact (hproper K hK).image continuous_neg

/-- **The first exit of a curve from a bounded open set.**

If a proper parametrization `γ` of a curve starts, at time `0`, inside a bounded open set
`U`, then it leaves `U` at a first time `b > 0`: the piece `γ([0,b))` stays in `U`, while
the endpoint `γ b` lies on the frontier of `U`.

This produces the two pieces of curve which, in the analysis of configuration BC of Fig. 7
in the proof of Lemma 8 of Klein–Langetepe–Nilforoushan (2009), are used to build the
crosscut of the neighbourhood `U` of Fig. 8(3): the segment `H` of `F⁻` adjacent to `w`,
and the piece of `G⁺` adjacent to `w`. -/
theorem IsProperLineParam.exists_first_exit {γ : ℝ → Plane} {Cu : Set Plane}
    (hγ : IsProperLineParam γ Cu) {U : Set Plane} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (h0 : γ 0 ∈ U) :
    ∃ b > (0 : ℝ), γ '' Ico 0 b ⊆ U ∧ γ b ∈ frontier U := by
  obtain ⟨hcont, -, -, hproper⟩ := hγ
  set B : Set ℝ := {t | 0 < t ∧ γ t ∉ U} with hBdef
  -- the curve does leave the bounded set `U`, since it is proper
  obtain ⟨M, hM⟩ := (hproper _ hUb.isCompact_closure).bddAbove
  have hBne : B.Nonempty := by
    refine ⟨max 1 (M + 1), lt_of_lt_of_le one_pos (le_max_left _ _), fun hmem => ?_⟩
    have h1 : max 1 (M + 1) ≤ M := hM (subset_closure hmem)
    have h2 : M + 1 ≤ max 1 (M + 1) := le_max_right _ _
    linarith
  have hBbdd : BddBelow B := ⟨0, fun t ht => ht.1.le⟩
  set b : ℝ := sInf B with hbdef
  have hb0 : 0 < b := by
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.1 (hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds h0))
    refine lt_of_lt_of_le hε (le_csInf hBne ?_)
    intro t ht
    by_contra hlt
    push Not at hlt
    exact ht.2 (hball (by
      rw [Real.ball_eq_Ioo]
      constructor <;> [linarith [ht.1]; linarith]))
  have hlow : ∀ t ∈ Ico (0 : ℝ) b, γ t ∈ U := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; exact h0
    · by_contra hc
      exact absurd (csInf_le hBbdd ⟨h, hc⟩) (not_le.2 ht.2)
  have hnotU : γ b ∉ U := by
    intro hmem
    obtain ⟨η, hη, hball⟩ :=
      Metric.mem_nhds_iff.1 (hcont.continuousAt.preimage_mem_nhds (hU.mem_nhds hmem))
    have hle : b + η ≤ b := by
      refine le_csInf hBne ?_
      intro t ht
      by_contra hlt
      push Not at hlt
      have hbt : b ≤ t := csInf_le hBbdd ht
      exact ht.2 (hball (by
        rw [Real.ball_eq_Ioo]
        constructor <;> linarith))
    linarith
  have hcl : γ b ∈ closure U := by
    have hbcl : b ∈ closure (Ico (0 : ℝ) b) := by
      rw [closure_Ico (ne_of_lt hb0)]
      exact ⟨hb0.le, le_refl b⟩
    have h2 := (hcont.continuousWithinAt (s := Ico (0 : ℝ) b)).mem_closure_image hbcl
    exact closure_mono (by rintro _ ⟨t, ht, rfl⟩; exact hlow t ht) h2
  refine ⟨b, hb0, ?_, ⟨hcl, by rwa [hU.interior_eq]⟩⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hlow t ht

/-- The backward form of `AVD.IsProperLineParam.exists_first_exit`: a proper parametrization
starting inside a bounded open set `U` at time `0` leaves it, in the direction of decreasing
parameter, at a first time `a < 0`, with `γ((a,0]) ⊆ U` and `γ a` on the frontier of `U`. -/
theorem IsProperLineParam.exists_first_exit_neg {γ : ℝ → Plane} {Cu : Set Plane}
    (hγ : IsProperLineParam γ Cu) {U : Set Plane} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (h0 : γ 0 ∈ U) :
    ∃ a < (0 : ℝ), γ '' Ioc a 0 ⊆ U ∧ γ a ∈ frontier U := by
  obtain ⟨b, hb, hsub, hfr⟩ :=
    hγ.reflect.exists_first_exit hU hUb (by simpa using h0)
  refine ⟨-b, by linarith, ?_, hfr⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hsub ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩

/-- If the branch of `γ` before `γ 0` stays in `A` but is not contained in `B`, then
arbitrarily close to `γ 0` there is a point of the branch lying in `A \ B`. -/
theorem exists_point_before {γ : ℝ → Plane} (hcont : Continuous γ) {A B U : Set Plane}
    (hA : BranchBefore γ A) (hB : ¬ BranchBefore γ B) (hU : U ∈ 𝓝 (γ 0)) :
    ∃ c < (0 : ℝ), γ c ∈ A ∧ γ c ∉ B ∧ γ c ∈ U := by
  obtain ⟨δ₁, hδ₁, hsub⟩ := hA
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcont.continuousAt.preimage_mem_nhds hU)
  set δ : ℝ := min δ₁ ε with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hε
  have hnot : ¬ γ '' Ioo (-δ) 0 ⊆ B := fun h => hB ⟨δ, hδ, h⟩
  obtain ⟨x, ⟨c, hc, rfl⟩, hxB⟩ := Set.not_subset.1 hnot
  refine ⟨c, hc.2, hsub ⟨c, ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δ₁ ε)) hc.1, hc.2⟩, rfl⟩,
    hxB, ?_⟩
  refine hball ?_
  rw [Real.ball_eq_Ioo]
  constructor
  · have : -ε ≤ -δ := neg_le_neg (min_le_right δ₁ ε)
    simp only [zero_sub]
    linarith [hc.1]
  · simp only [zero_add]
    linarith [hc.2, hε]

/-- The mirror image of `exists_point_before` for the branch after `γ 0`. -/
theorem exists_point_after {γ : ℝ → Plane} (hcont : Continuous γ) {A B U : Set Plane}
    (hA : BranchAfter γ A) (hB : ¬ BranchAfter γ B) (hU : U ∈ 𝓝 (γ 0)) :
    ∃ c > (0 : ℝ), γ c ∈ A ∧ γ c ∉ B ∧ γ c ∈ U := by
  obtain ⟨δ₁, hδ₁, hsub⟩ := hA
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcont.continuousAt.preimage_mem_nhds hU)
  set δ : ℝ := min δ₁ ε with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hε
  have hnot : ¬ γ '' Ioo 0 δ ⊆ B := fun h => hB ⟨δ, hδ, h⟩
  obtain ⟨x, ⟨c, hc, rfl⟩, hxB⟩ := Set.not_subset.1 hnot
  refine ⟨c, hc.1, hsub ⟨c, ⟨hc.1, lt_of_lt_of_le hc.2 (min_le_left δ₁ ε)⟩, rfl⟩, hxB, ?_⟩
  refine hball ?_
  rw [Real.ball_eq_Ioo]
  constructor
  · simp only [zero_sub]
    linarith [hc.1, hε]
  · simp only [zero_add]
    have : δ ≤ ε := min_le_right δ₁ ε
    linarith [hc.2]

/-- Two conditions satisfied by the branch of a curve before its base point are satisfied
simultaneously by a shorter branch. -/
theorem BranchBefore.inter {γ : ℝ → Plane} {A B : Set Plane} (hA : BranchBefore γ A)
    (hB : BranchBefore γ B) : BranchBefore γ (A ∩ B) := by
  obtain ⟨δ₁, h₁, hs₁⟩ := hA
  obtain ⟨δ₂, h₂, hs₂⟩ := hB
  refine ⟨min δ₁ δ₂, lt_min h₁ h₂, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  exact ⟨hs₁ ⟨c, ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δ₁ δ₂)) hc.1, hc.2⟩, rfl⟩,
    hs₂ ⟨c, ⟨lt_of_le_of_lt (neg_le_neg (min_le_right δ₁ δ₂)) hc.1, hc.2⟩, rfl⟩⟩

/-- Two conditions satisfied by the branch of a curve after its base point are satisfied
simultaneously by a shorter branch. -/
theorem BranchAfter.inter {γ : ℝ → Plane} {A B : Set Plane} (hA : BranchAfter γ A)
    (hB : BranchAfter γ B) : BranchAfter γ (A ∩ B) := by
  obtain ⟨δ₁, h₁, hs₁⟩ := hA
  obtain ⟨δ₂, h₂, hs₂⟩ := hB
  refine ⟨min δ₁ δ₂, lt_min h₁ h₂, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  exact ⟨hs₁ ⟨c, ⟨hc.1, lt_of_lt_of_le hc.2 (min_le_left δ₁ δ₂)⟩, rfl⟩,
    hs₂ ⟨c, ⟨hc.1, lt_of_lt_of_le hc.2 (min_le_right δ₁ δ₂)⟩, rfl⟩⟩

namespace CurveSystem

variable {S : Finset ι} {C : CurveSystem S}

/-- The closed Jordan curve behind the proof of **Lemma 6** of
Klein–Langetepe–Nilforoushan (2009).

Two points `g u`, `g v` of the curve `J(p,r)` lying in the open half-plane `D(p,q)` are
joined by an arc `π` through `VR(p,{p,q,r})` and by an arc `ρ` through `VR(r,{p,q,r})`
(Facts 1 and 2 of the proof of Lemma 6); their union is a closed Jordan curve, whose
bounded complementary domain `Dm` contains the piece `g((u,v))` of `J(p,r)` between the two
points, while the two unbounded pieces `g((-∞,u))` and `g((v,∞))` stay in the unbounded
complementary domain `Em`:

> Together, arcs `π ⊆ VR(p,S)` and `ρ ⊆ VR(r,S)` form a closed Jordan curve; let `D` denote
> its interior domain.  […]  Therefore, the segment of `J(p,r)` between `a₂` and `a₄` is
> fully contained in domain `D`, while the two unbounded complementary segments of `J(p,r)`
> stay outside.

This is the first half of the proof of Lemma 6; it is stated separately because the same
construction is used again in the analysis of configuration AA of Fig. 7 in the proof of
Lemma 8 (`AVD.CurveSystem.aa_configuration_impossible`). -/
theorem exists_lemma6_jordan_domain (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p r))
    {u v : ℝ} (huv : u < v) (hgu : g u ∈ C.D p q) (hgv : g v ∈ C.D p q) :
    ∃ π ρ : ℝ → Plane, ∃ Dm Em : Set Plane,
      IsArc π ∧ π 0 = g u ∧ π 1 = g v ∧ π '' Ioo 0 1 ⊆ C.VR p {p, q, r} ∧
      IsArc ρ ∧ ρ 0 = g u ∧ ρ 1 = g v ∧ ρ '' Ioo 0 1 ⊆ C.VR r {p, q, r} ∧
      IsOpen Dm ∧ IsOpen Em ∧ IsConnected Dm ∧ Disjoint Dm Em ∧
      Dm ∪ Em = (π '' Icc 0 1 ∪ ρ '' Icc 0 1)ᶜ ∧
      frontier Dm = π '' Icc 0 1 ∪ ρ '' Icc 0 1 ∧ Bornology.IsBounded Dm ∧
      g '' Ioo u v ⊆ Dm ∧ g '' Iio u ⊆ Em ∧ g '' Ioi v ⊆ Em := by
  obtain ⟨hgcont, hginj, hgrange, hgproper⟩ := hg
  set T : Finset ι := {p, q, r} with hTdef
  have hTS : T ⊆ S := by
    intro x hx
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hpT : p ∈ T := by simp [hTdef]
  have hrT : r ∈ T := by simp [hTdef]
  have hVRp : C.VR p T = C.D p q ∩ C.D p r := VR_triple hTdef hpq hpr
  have hVRr : C.VR r T = C.D r p ∩ C.D r q :=
    VR_triple (by rw [hTdef]; ext x; simp; tauto) (Ne.symm hpr) (Ne.symm hqr)
  have hmemJ : ∀ x : ℝ, g x ∈ C.J p r := fun x => hgrange ▸ mem_range_self x
  -- Fact 1: points of `J(p,r)` inside `D(p,q)` are accessible from `VR(p,S)`
  have haccp : ∀ x : ℝ, g x ∈ C.D p q → AccessibleFrom (C.VR p T) (g x) := by
    intro x hx
    have h := accessibleFrom_of_mem_J hadm hp hr hpr (hmemJ x)
      ((C.D_isOpen p hp q hq hpq).mem_nhds hx)
    rw [hVRp]
    exact h
  -- Fact 2: they are also accessible from `VR(r,S)`, by Lemma 5
  have haccr : ∀ x : ℝ, g x ∈ C.D p q → AccessibleFrom (C.VR r T) (g x) := by
    intro x hx
    have hJ : g x ∈ C.J r p := by rw [C.J_symm hr hp (Ne.symm hpr)]; exact hmemJ x
    have h := accessibleFrom_of_mem_J hadm hr hp (Ne.symm hpr) hJ
      ((C.D_isOpen p hp q hq hpq).mem_nhds hx)
    refine h.mono ?_
    rw [hVRr]
    rintro y ⟨hy1, hy2⟩
    exact ⟨hy2, lemma5 hadm hr hp hq (Ne.symm hpr) hpq (Ne.symm hqr) ⟨hy2, hy1⟩⟩
  have hne_uv : g u ≠ g v := fun h => absurd (hginj h) (ne_of_lt huv)
  obtain ⟨π, hπarc, hπ0, hπ1, hπint⟩ := exists_arc_of_accessible (VR_isOpen hTS hp)
    (hadm.A2 T hTS p hpT) hne_uv (haccp u hgu) (haccp v hgv)
  obtain ⟨ρ, hρarc, hρ0, hρ1, hρint⟩ := exists_arc_of_accessible (VR_isOpen hTS hr)
    (hadm.A2 T hTS r hrT) hne_uv (haccr u hgu) (haccr v hgv)
  -- the two arcs `π` and `ρ` form a closed Jordan curve `Γ`
  have hdisjπρ : Disjoint (π '' Ioo 0 1) (ρ '' Ioo 0 1) :=
    Disjoint.mono hπint hρint (VR_disjoint hTS hpT hrT hpr)
  set Γ : Set Plane := π '' Icc 0 1 ∪ ρ '' Icc 0 1 with hΓdef
  have hΓ : IsClosedJordanCurve Γ :=
    isClosedJordanCurve_of_arcs hπarc hρarc (by rw [hπ0, hρ0]) (by rw [hπ1, hρ1]) hdisjπρ
  have hguΓ : g u ∈ Γ := Or.inl ⟨0, ⟨le_refl 0, by norm_num⟩, hπ0⟩
  have hgvΓ : g v ∈ Γ := Or.inl ⟨1, ⟨by norm_num, le_refl 1⟩, hπ1⟩
  have hΓsub : Γ ⊆ (C.VR p T ∪ C.VR r T) ∪ {g u, g v} := by
    rintro x (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · rcases eq_or_lt_of_le hc.1 with h | h
      · exact Or.inr (Or.inl (by rw [← h, hπ0]))
      · rcases eq_or_lt_of_le hc.2 with h' | h'
        · exact Or.inr (Or.inr (by rw [h', hπ1]; rfl))
        · exact Or.inl (Or.inl (hπint ⟨c, ⟨h, h'⟩, rfl⟩))
    · rcases eq_or_lt_of_le hc.1 with h | h
      · exact Or.inr (Or.inl (by rw [← h, hρ0, ← hπ0]))
      · rcases eq_or_lt_of_le hc.2 with h' | h'
        · exact Or.inr (Or.inr (by rw [h', hρ1, ← hπ1]; rfl))
        · exact Or.inl (Or.inr (hρint ⟨c, ⟨h, h'⟩, rfl⟩))
  have hΓJ : ∀ x ∈ Γ, x ∈ C.J p r → x = g u ∨ x = g v := by
    intro x hx hxJ
    rcases hΓsub hx with (h | h) | h
    · exact absurd ((hVRp ▸ h : x ∈ C.D p q ∩ C.D p r).2)
        (notMem_D_of_mem_J hp hr hpr hxJ).1
    · exact absurd ((hVRr ▸ h : x ∈ C.D r p ∩ C.D r q).1)
        (notMem_D_of_mem_J hp hr hpr hxJ).2
    · simpa using h
  obtain ⟨D₁, D₂, hO1, hO2, hc1, hc2, hd12, hu12, hf1, hf2, hbdd⟩ :=
    hΓ.exists_separation_frontier_eq
  -- the position of the three pieces of `J(p,r)`, for the bounded complementary domain
  have main : ∀ Dm Em : Set Plane, IsOpen Dm → IsOpen Em → IsConnected Dm → Disjoint Dm Em →
      Dm ∪ Em = Γᶜ → frontier Dm = Γ → Bornology.IsBounded Dm →
      ¬ Bornology.IsBounded Em →
      g '' Ioo u v ⊆ Dm ∧ g '' Iio u ⊆ Em ∧ g '' Ioi v ⊆ Em := by
    intro Dm Em hOD hOE hcD hdDE hun hfD hbD hnbE
    have hDsub : Dm ⊆ Γᶜ := hun ▸ subset_union_left
    have hpiece : ∀ A : Set ℝ, IsPreconnected A → u ∉ A → v ∉ A →
        g '' A ⊆ Dm ∨ g '' A ⊆ Em := by
      intro A hA huA hvA
      refine (hA.image g hgcont.continuousOn).subset_or_subset hOD hOE hdDE ?_
      rw [hun]
      rintro x ⟨c, hc, rfl⟩ hxΓ
      rcases hΓJ _ hxΓ (hmemJ c) with h | h
      · exact huA (hginj h ▸ hc)
      · exact hvA (hginj h ▸ hc)
    have hray : ∀ A : Set ℝ, ¬ BddBelow A ∨ ¬ BddAbove A → ¬ Bornology.IsBounded (g '' A) := by
      intro A hA hb
      have hcomp : IsCompact (g ⁻¹' closure (g '' A)) := hgproper _ hb.isCompact_closure
      have hAsub : A ⊆ g ⁻¹' closure (g '' A) := fun c hc => subset_closure ⟨c, hc, rfl⟩
      rcases hA with h | h
      · exact h (BddBelow.mono hAsub hcomp.bddBelow)
      · exact h (BddAbove.mono hAsub hcomp.bddAbove)
    have hIio : g '' Iio u ⊆ Em := by
      rcases hpiece (Iio u) isPreconnected_Iio (by simp) (by simpa using huv.le) with h | h
      · exact absurd (hbD.subset h) (hray _ (Or.inl (not_bddBelow_Iio u)))
      · exact h
    have hIoi : g '' Ioi v ⊆ Em := by
      rcases hpiece (Ioi v) isPreconnected_Ioi (by simpa using huv.le) (by simp) with h | h
      · exact absurd (hbD.subset h) (hray _ (Or.inr (not_bddAbove_Ioi v)))
      · exact h
    refine ⟨?_, hIio, hIoi⟩
    rcases hpiece (Ioo u v) isPreconnected_Ioo (by simp) (by simp) with h | h
    · exact h
    · exfalso
      have hcurve : ∀ c : ℝ, g c ∈ Em ∨ g c ∈ Γ := by
        intro c
        rcases lt_trichotomy c u with hc | hc | hc
        · exact Or.inl (hIio ⟨c, hc, rfl⟩)
        · exact Or.inr (hc ▸ hguΓ)
        · rcases lt_trichotomy c v with hc' | hc' | hc'
          · exact Or.inl (h ⟨c, ⟨hc, hc'⟩, rfl⟩)
          · exact Or.inr (hc' ▸ hgvΓ)
          · exact Or.inl (hIoi ⟨c, hc', rfl⟩)
      have hJdisj : ∀ x ∈ C.J p r, x ∉ Dm := by
        intro x hx hmem
        rw [← hgrange] at hx
        obtain ⟨c, rfl⟩ := hx
        rcases hcurve c with hcE | hcΓ
        · exact (Set.disjoint_left.1 hdDE hmem) hcE
        · exact (hDsub hmem) hcΓ
      have hDmsub : Dm ⊆ C.D p r ∪ C.D r p := by
        intro x hx
        have hx' : x ∈ (C.J p r)ᶜ := fun h => hJdisj x h hx
        rw [C.compl_J p hp r hr hpr] at hx'
        exact hx'
      have hhalf : (1 : ℝ)/2 ∈ Ioo (0 : ℝ) 1 := by norm_num
      have hπhalf : π (1/2) ∈ C.D p r :=
        (hVRp ▸ hπint ⟨1/2, hhalf, rfl⟩ : π (1/2) ∈ C.D p q ∩ C.D p r).2
      have hρhalf : ρ (1/2) ∈ C.D r p :=
        (hVRr ▸ hρint ⟨1/2, hhalf, rfl⟩ : ρ (1/2) ∈ C.D r p ∩ C.D r q).1
      have hπΓ : π (1/2) ∈ Γ := Or.inl ⟨1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
      have hρΓ : ρ (1/2) ∈ Γ := Or.inr ⟨1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
      have hclD : Γ ⊆ closure Dm := by rw [← hfD]; exact frontier_subset_closure
      rcases hcD.isPreconnected.subset_or_subset (C.D_isOpen p hp r hr hpr)
        (C.D_isOpen r hr p hp (Ne.symm hpr)) (C.D_disjoint p hp r hr hpr) hDmsub with hD | hD
      · have hmem : ρ (1/2) ∈ closure (C.D p r) := closure_mono hD (hclD hρΓ)
        rw [closure_D_eq hadm hp hr hpr] at hmem
        rcases hmem with h' | h'
        · exact (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) h' hρhalf
        · exact (notMem_D_of_mem_J hp hr hpr h').2 hρhalf
      · have hmem : π (1/2) ∈ closure (C.D r p) := closure_mono hD (hclD hπΓ)
        rw [closure_D_eq hadm hr hp (Ne.symm hpr)] at hmem
        rcases hmem with h' | h'
        · exact (Set.disjoint_left.1 (C.D_disjoint r hr p hp (Ne.symm hpr))) h' hπhalf
        · exact (notMem_D_of_mem_J hr hp (Ne.symm hpr) h').2 hπhalf
  rcases hbdd with ⟨hb1, hnb2⟩ | ⟨hb2, hnb1⟩
  · obtain ⟨h1, h2, h3⟩ := main D₁ D₂ hO1 hO2 hc1 hd12 hu12 hf1 hb1 hnb2
    exact ⟨π, ρ, D₁, D₂, hπarc, hπ0, hπ1, hπint, hρarc, hρ0, hρ1, hρint, hO1, hO2, hc1,
      hd12, hu12, hf1, hb1, h1, h2, h3⟩
  · have hu21 : D₂ ∪ D₁ = Γᶜ := by rw [union_comm]; exact hu12
    obtain ⟨h1, h2, h3⟩ := main D₂ D₁ hO2 hO1 hc2 hd12.symm hu21 hf2 hb2 hnb1
    exact ⟨π, ρ, D₂, D₁, hπarc, hπ0, hπ1, hπint, hρarc, hρ0, hρ1, hρint, hO2, hO1, hc2,
      hd12.symm, hu21, hf2, hb2, h1, h2, h3⟩

/-- The key step in the proof of **Lemma 6** of Klein–Langetepe–Nilforoushan (2009).

Suppose that the curve `J(p,r)` visits, in this order, two points `g u, g v ∈ D(p,q)` and
two points `g s, g t ∈ D(q,p)`, where `g s` lies between `g u` and `g v` on the curve while
`g t` does not.  This is impossible.

The proof follows the paper: the points `g u, g v` are joined by an arc `π` through
`VR(p,S)` and by an arc `ρ` through `VR(r,S)` (Facts 1 and 2), the points `g s, g t` are
joined by an arc `σ` through `VR(q,S)` (Fact 3); the closed Jordan curve `π ∪ ρ` bounds a
domain `D` which contains the piece of `J(p,r)` between `g u` and `g v`, hence `g s`, while
`g t` lies outside (this is `AVD.CurveSystem.exists_lemma6_jordan_domain`); the arc `σ` can
cross neither `π` nor `ρ`, a contradiction. -/
theorem lemma6_core (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p r))
    {u v s t : ℝ} (huv : u < v) (hus : u < s) (hsv : s < v) (ht : t < u ∨ v < t)
    (hgu : g u ∈ C.D p q) (hgv : g v ∈ C.D p q)
    (hgs : g s ∈ C.D q p) (hgt : g t ∈ C.D q p) : False := by
  obtain ⟨π, ρ, Dm, Em, hπarc, hπ0, hπ1, hπint, hρarc, hρ0, hρ1, hρint, hOD, hOE, -,
    hdDE, hun, -, -, hmid, hIio, hIoi⟩ :=
    exists_lemma6_jordan_domain hadm hp hq hr hpq hqr hpr hg huv hgu hgv
  obtain ⟨hgcont, hginj, hgrange, hgproper⟩ := hg
  set T : Finset ι := {p, q, r} with hTdef
  have hTS : T ⊆ S := by
    intro x hx
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hpT : p ∈ T := by simp [hTdef]
  have hqT : q ∈ T := by simp [hTdef]
  have hrT : r ∈ T := by simp [hTdef]
  have hVRq : C.VR q T = C.D q p ∩ C.D q r :=
    VR_triple (by rw [hTdef]; ext x; simp; tauto) (Ne.symm hpq) hqr
  have hmemJ : ∀ x : ℝ, g x ∈ C.J p r := fun x => hgrange ▸ mem_range_self x
  -- Fact 3: points of `J(p,r)` inside `D(q,p)` are accessible from `VR(q,S)`
  have haccq : ∀ x : ℝ, g x ∈ C.D q p → AccessibleFrom (C.VR q T) (g x) := by
    intro x hx
    have h := accessibleFrom_of_mem_J hadm hp hr hpr (hmemJ x)
      ((C.D_isOpen q hq p hp (Ne.symm hpq)).mem_nhds hx)
    refine h.mono ?_
    rw [hVRq]
    rintro y ⟨hy1, hy2⟩
    exact ⟨hy1, lemma5 hadm hq hp hr (Ne.symm hpq) hpr hqr ⟨hy1, hy2⟩⟩
  have hst : s ≠ t := by
    rcases ht with h | h
    · exact ne_of_gt (by linarith)
    · exact ne_of_lt (by linarith)
  have hne_st : g s ≠ g t := fun h => absurd (hginj h) hst
  obtain ⟨σ, hσarc, hσ0, hσ1, hσint⟩ := exists_arc_of_accessible (VR_isOpen hTS hq)
    (hadm.A2 T hTS q hqT) hne_st (haccq s hgs) (haccq t hgt)
  set Γ : Set Plane := π '' Icc 0 1 ∪ ρ '' Icc 0 1 with hΓdef
  have hΓsub : Γ ⊆ (C.VR p T ∪ C.VR r T) ∪ {g u, g v} := by
    rintro x (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · rcases eq_or_lt_of_le hc.1 with h | h
      · exact Or.inr (Or.inl (by rw [← h, hπ0]))
      · rcases eq_or_lt_of_le hc.2 with h' | h'
        · exact Or.inr (Or.inr (by rw [h', hπ1]; rfl))
        · exact Or.inl (Or.inl (hπint ⟨c, ⟨h, h'⟩, rfl⟩))
    · rcases eq_or_lt_of_le hc.1 with h | h
      · exact Or.inr (Or.inl (by rw [← h, hρ0, ← hπ0]))
      · rcases eq_or_lt_of_le hc.2 with h' | h'
        · exact Or.inr (Or.inr (by rw [h', hρ1, ← hπ1]; rfl))
        · exact Or.inl (Or.inr (hρint ⟨c, ⟨h, h'⟩, rfl⟩))
  have hΓq : ∀ x ∈ Γ, x ∉ C.VR q T := by
    intro x hx hxq
    rcases hΓsub hx with (h | h) | h
    · exact (Set.disjoint_left.1 (VR_disjoint hTS hpT hqT hpq)) h hxq
    · exact (Set.disjoint_left.1 (VR_disjoint hTS hrT hqT (Ne.symm hqr))) h hxq
    · have hxD : x ∈ C.D p q := by
        rcases (by simpa using h : x = g u ∨ x = g v) with rfl | rfl
        · exact hgu
        · exact hgv
      exact (Set.disjoint_left.1 (C.D_disjoint p hp q hq hpq)) hxD
        ((hVRq ▸ hxq : x ∈ C.D q p ∩ C.D q r).1)
  have hDsub : Dm ⊆ Γᶜ := hun ▸ subset_union_left
  have hEsub : Em ⊆ Γᶜ := hun ▸ subset_union_right
  -- `g s` is inside the bounded domain, `g t` outside
  have hgsD : g s ∈ Dm := hmid ⟨s, ⟨hus, hsv⟩, rfl⟩
  have hgtE : g t ∈ Em := by
    rcases ht with h | h
    · exact hIio ⟨t, h, rfl⟩
    · exact hIoi ⟨t, h, rfl⟩
  -- but the arc `σ` joining them avoids `Γ`
  have hσsub : σ '' Icc 0 1 ⊆ Dm ∪ Em := by
    rw [hun]
    rintro x ⟨c, hc, rfl⟩ hxΓ
    rcases eq_or_lt_of_le hc.1 with h | h
    · refine (hDsub hgsD) ?_
      rw [← hσ0, h]
      exact hxΓ
    · rcases eq_or_lt_of_le hc.2 with h' | h'
      · refine (hEsub hgtE) ?_
        rw [← hσ1, ← h']
        exact hxΓ
      · exact hΓq _ hxΓ (hσint ⟨c, ⟨h, h'⟩, rfl⟩)
  rcases (isPreconnected_Icc.image σ hσarc.cont).subset_or_subset hOD hOE hdDE hσsub with
    h | h
  · refine (Set.disjoint_left.1 hdDE (h ⟨1, ⟨by norm_num, le_refl 1⟩, rfl⟩)) ?_
    rw [hσ1]; exact hgtE
  · refine (Set.disjoint_left.1 hdDE ?_) (h ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩)
    rw [hσ0]; exact hgsD

end CurveSystem

end AVD
