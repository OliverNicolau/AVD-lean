import AbstractVoronoi.Imports

/-!
# Jordan curves, the sphere, and axiom `A₁`

This file sets up the ambient plane, closed Jordan curves in an arbitrary topological space,
the unit sphere `S²` with its stereographic projection to the plane, and the notion of an
*unbounded Jordan curve* used in axiom `A₁` of Definition 1 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

Axiom `A₁` of the paper reads

> Each curve `J(p,q)`, where `p, q ∈ S`, is mapped to a closed Jordan curve through the
> north pole by stereographic projection to the sphere,

and this is exactly how `IsUnboundedJordanCurve` is defined here: a set `C` of the plane is
an unbounded Jordan curve if its inverse stereographic image, together with the north pole,
is a closed Jordan curve of the sphere.

The main result of the file is `IsUnboundedJordanCurve.exists_properParam`: such a curve
admits a *proper parametrization* `ℝ → ℝ²`, i.e. a proper continuous injection of the line
onto `C`.  This is the form in which the curves are used in the later proofs (points
"consecutively visited" by a curve, Lemma 6 of the paper).
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- The Euclidean plane `ℝ²`, the ambient space of the paper. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-! ## Closed Jordan curves -/

/-- A *closed Jordan curve* in a topological space: a homeomorphic image of the circle,
presented as the image of a closed curve `γ : [0,1] → X` (`γ 0 = γ 1`) which is injective on
`[0,1)`.

The statement is made for an arbitrary topological space because the paper uses closed
Jordan curves both in the plane and on the sphere (axiom `A₁` of Definition 1 of
Klein–Langetepe–Nilforoushan (2009)). -/
def IsClosedJordanCurve {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Ico 0 1) ∧ γ 0 = γ 1 ∧
    γ '' Icc 0 1 = C

/-- A closed Jordan curve can be parametrized starting at any prescribed one of its points:
if `x ∈ C`, then `C` has a parametrization `γ` with `γ 0 = x`.  (The parametrization is
obtained from any other one by a cyclic rotation of the parameter.) -/
theorem IsClosedJordanCurve.exists_param_at {X : Type*} [TopologicalSpace X] {C : Set X}
    (h : IsClosedJordanCurve C) {x : X} (hx : x ∈ C) :
    ∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Ico 0 1) ∧ γ 0 = γ 1 ∧
      γ '' Icc 0 1 = C ∧ γ 0 = x := by
  classical
  obtain ⟨σ, hcont, hinj, hclosed, himg⟩ := h
  obtain ⟨t₀, ht₀, hσt₀⟩ : ∃ t₀ ∈ Icc (0 : ℝ) 1, σ t₀ = x := by
    rw [← himg] at hx
    obtain ⟨t, ht, hσt⟩ := hx
    exact ⟨t, ht, hσt⟩
  -- the rotated parametrization
  set γ : ℝ → X := fun t => if t + t₀ ≤ 1 then σ (t + t₀) else σ (t + t₀ - 1) with hγdef
  have hlow : ∀ t : ℝ, t + t₀ ≤ 1 → γ t = σ (t + t₀) := by
    intro t ht; simp [hγdef, ht]
  have hhigh : ∀ t : ℝ, ¬ (t + t₀ ≤ 1) → γ t = σ (t + t₀ - 1) := by
    intro t ht; simp [hγdef, ht]
  have hcont' : ContinuousOn γ (Icc 0 1) := by
    have h1 : ContinuousOn (fun t : ℝ => σ (t + t₀)) (Icc 0 1 ∩ Iic (1 - t₀)) := by
      refine hcont.comp (by fun_prop) ?_
      rintro t ⟨ht, ht'⟩
      exact ⟨by linarith [ht.1, ht₀.1], by simpa using by linarith [mem_Iic.1 ht']⟩
    have h2 : ContinuousOn (fun t : ℝ => σ (t + t₀ - 1)) (Icc 0 1 ∩ closure (Iic (1 - t₀))ᶜ) := by
      refine hcont.comp (by fun_prop) ?_
      rintro t ⟨ht, ht'⟩
      rw [compl_Iic, closure_Ioi] at ht'
      exact ⟨by linarith [mem_Ici.1 ht'], by linarith [ht.2, ht₀.2]⟩
    have hpw : ContinuousOn (Set.piecewise (Iic (1 - t₀)) (fun t : ℝ => σ (t + t₀))
        (fun t : ℝ => σ (t + t₀ - 1))) (Icc 0 1) := by
      refine ContinuousOn.piecewise ?_ ?_ ?_
      · rintro t ⟨-, ht⟩
        have ht' : t = 1 - t₀ := by simpa [frontier_Iic] using ht
        subst ht'
        rw [show (1 : ℝ) - t₀ + t₀ = 1 by ring, show (1 : ℝ) - 1 = 0 by ring, hclosed]
      · exact h1.mono (by
          intro t ht
          exact ⟨ht.1, by simpa using ht.2⟩)
      · exact h2.mono (by
          intro t ht
          exact ⟨ht.1, ht.2⟩)
    refine hpw.congr ?_
    intro t _
    by_cases h : t + t₀ ≤ 1
    · rw [hlow t h, Set.piecewise_eq_of_mem _ _ _ (by simp; linarith)]
    · rw [hhigh t h, Set.piecewise_eq_of_notMem _ _ _ (by simp; linarith [not_le.1 h])]
  -- the rotation is a bijection of `[0,1)` with itself, up to the identification `0 ∼ 1`
  have hval : ∀ t ∈ Ico (0 : ℝ) 1, ∃ s ∈ Ico (0 : ℝ) 1, γ t = σ s ∧
      (t + t₀ ≤ 1 → s = t + t₀ ∨ (t + t₀ = 1 ∧ s = 0)) ∧
      (¬ (t + t₀ ≤ 1) → s = t + t₀ - 1) := by
    intro t ht
    by_cases h : t + t₀ ≤ 1
    · rcases eq_or_lt_of_le h with heq | hlt
      · refine ⟨0, ⟨le_refl 0, one_pos⟩, ?_, ?_, ?_⟩
        · rw [hlow t h, heq, ← hclosed]
        · intro _; exact Or.inr ⟨heq, rfl⟩
        · intro hc; exact absurd h hc
      · exact ⟨t + t₀, ⟨by linarith [ht.1, ht₀.1], hlt⟩, hlow t h, fun _ => Or.inl rfl,
          fun hc => absurd h hc⟩
    · exact ⟨t + t₀ - 1, ⟨by linarith [not_le.1 h], by linarith [ht.2, ht₀.2]⟩,
        hhigh t h, fun hc => absurd hc h, fun _ => rfl⟩
  have hinj' : InjOn γ (Ico 0 1) := by
    intro a ha b hb hab
    obtain ⟨sa, hsa, hγa, hla, hha⟩ := hval a ha
    obtain ⟨sb, hsb, hγb, hlb, hhb⟩ := hval b hb
    have hs : sa = sb := hinj hsa hsb (by rw [← hγa, ← hγb, hab])
    by_cases hA : a + t₀ ≤ 1 <;> by_cases hB : b + t₀ ≤ 1
    · rcases hla hA with rfl | ⟨he1, rfl⟩ <;> rcases hlb hB with h2 | ⟨he2, h2⟩
      · linarith [hs ▸ h2]
      · -- `sa = a + t₀ = 0` while `b + t₀ = 1`
        exfalso
        rw [h2] at hs
        have : a + t₀ = 0 := hs
        have ha0 : a = 0 := by linarith [ht₀.1, ha.1, this]
        have : t₀ = 0 := by linarith
        rw [this] at he2
        simp only [add_zero] at he2
        linarith [hb.2]
      · exfalso
        rw [h2] at hs
        have : b + t₀ = 0 := hs.symm
        have : t₀ = 0 := by linarith [hb.1, ht₀.1]
        rw [this] at he1
        simp only [add_zero] at he1
        linarith [ha.2]
      · linarith
    · exfalso
      rw [hhb (by exact hB)] at hs
      rcases hla hA with rfl | ⟨he1, h1⟩
      · linarith [ha.1, hb.2, hs]
      · rw [h1] at hs
        have : b + t₀ = 1 := by linarith [hs]
        exact hB (le_of_eq this)
    · exfalso
      rw [hha (by exact hA)] at hs
      rcases hlb hB with rfl | ⟨he2, h2⟩
      · linarith [hb.1, ha.2, hs]
      · rw [h2] at hs
        have : a + t₀ = 1 := by linarith [hs]
        exact hA (le_of_eq this)
    · rw [hha (by exact hA), hhb (by exact hB)] at hs
      linarith
  have himg' : γ '' Icc 0 1 = C := by
    apply Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      rw [← himg]
      by_cases h : t + t₀ ≤ 1
      · exact ⟨t + t₀, ⟨by linarith [ht.1, ht₀.1], h⟩, (hlow t h).symm⟩
      · exact ⟨t + t₀ - 1, ⟨by linarith [not_le.1 h], by linarith [ht.2, ht₀.2]⟩,
          (hhigh t h).symm⟩
    · intro y hy
      rw [← himg] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      by_cases h : t₀ ≤ s
      · refine ⟨s - t₀, ⟨by linarith, by linarith [hs.2, ht₀.1]⟩, ?_⟩
        rw [hlow _ (by linarith [hs.2])]
        ring_nf
      · rcases eq_or_lt_of_le hs.1 with h0 | h0
        · -- `s = 0`: the parameter is `1 - t₀`, and `σ 1 = σ 0`
          refine ⟨1 - t₀, ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩, ?_⟩
          rw [hlow _ (by linarith), show (1 : ℝ) - t₀ + t₀ = 1 by ring, ← hclosed, ← h0]
        · refine ⟨s - t₀ + 1, ⟨by linarith [hs.1, ht₀.2], by linarith [not_le.1 h]⟩, ?_⟩
          rw [hhigh _ (by intro hc; linarith), show s - t₀ + 1 + t₀ - 1 = s by ring]
  refine ⟨γ, hcont', hinj', ?_, himg', ?_⟩
  · by_cases h0 : (0 : ℝ) + t₀ ≤ 1
    · rw [hlow 0 h0]
      by_cases h1 : (1 : ℝ) + t₀ ≤ 1
      · have : t₀ = 0 := by linarith [ht₀.1]
        rw [hlow 1 h1, this]
        simpa using hclosed
      · rw [hhigh 1 h1]
        ring_nf
    · exact absurd (by linarith [ht₀.2] : (0 : ℝ) + t₀ ≤ 1) h0
  · rw [hlow 0 (by linarith [ht₀.2]), zero_add, hσt₀]

/-! ## The sphere and the stereographic projection -/

/-- The ambient space `ℝ³` of the sphere `S²` has dimension `2 + 1`; this instance is what
lets `Mathlib`'s stereographic projection be used on `S²`. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-- The unit sphere `S² ⊆ ℝ³`, the target of the stereographic projection used in axiom
`A₁` of Definition 1 of Klein–Langetepe–Nilforoushan (2009). -/
abbrev Sphere : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The *north pole* of the sphere `S²`, the point through which the stereographic images of
the bisecting curves pass (axiom `A₁` of Definition 1 of
Klein–Langetepe–Nilforoushan (2009)). -/
def northPole : Sphere := ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The stereographic projection of the sphere `S²` from its north pole onto the plane `ℝ²`.
It is a homeomorphism of `S² \ {north pole}` onto `ℝ²`; this is the projection used in
axiom `A₁` of Definition 1 of Klein–Langetepe–Nilforoushan (2009). -/
def stereo : OpenPartialHomeomorph Sphere Plane := stereographic' 2 northPole

@[simp] theorem stereo_source : stereo.source = {northPole}ᶜ := by simp [stereo]

@[simp] theorem stereo_target : stereo.target = univ := by simp [stereo]

/-- The inverse stereographic image of a point of the plane avoids the north pole, i.e. lies
in the source of the stereographic projection. -/
theorem stereo_symm_apply_mem_source (x : Plane) : stereo.symm x ∈ stereo.source :=
  stereo.map_target (by simp)

/-- No point of the plane is sent to the north pole by the inverse stereographic projection. -/
theorem stereo_symm_ne_northPole (x : Plane) : stereo.symm x ≠ northPole := by
  have := stereo_symm_apply_mem_source x
  rw [stereo_source] at this
  simpa using this

/-- The stereographic projection is a left inverse of its inverse: every point of the plane
is the projection of a point of the sphere different from the north pole. -/
theorem stereo_stereo_symm (x : Plane) : stereo (stereo.symm x) = x :=
  stereo.right_inv (by simp)

/-- The inverse stereographic projection is a left inverse of the stereographic projection
away from the north pole. -/
theorem stereo_symm_stereo {z : Sphere} (hz : z ≠ northPole) : stereo.symm (stereo z) = z :=
  stereo.left_inv (by simpa using hz)

/-- The inverse stereographic projection is continuous on the whole plane. -/
theorem continuous_stereo_symm : Continuous (stereo.symm : Plane → Sphere) := by
  have h := stereo.symm.continuousOn_toFun
  rw [show stereo.symm.source = univ by simp [stereo]] at h
  exact continuousOn_univ.1 h

/-- The inverse stereographic projection is injective. -/
theorem stereo_symm_injective : Function.Injective (stereo.symm : Plane → Sphere) :=
  Function.LeftInverse.injective (g := (stereo : Sphere → Plane)) fun x => stereo_stereo_symm x

/-! ## Unbounded Jordan curves: axiom `A₁` -/

/-- The *completion on the sphere* of a plane set `C`: the inverse stereographic image of
`C`, together with the north pole.  Cf. footnote 4 of
Klein–Langetepe–Nilforoushan (2009). -/
def sphereCompletion (C : Set Plane) : Set Sphere := stereo.symm '' C ∪ {northPole}

/-- An *unbounded Jordan curve* of the plane, in the sense of axiom `A₁` of Definition 1 of
Klein–Langetepe–Nilforoushan (2009):

> Each curve `J(p,q)`, where `p, q ∈ S`, is mapped to a closed Jordan curve through the north
> pole by stereographic projection to the sphere.

That is, `C` is an unbounded Jordan curve if its stereographic image on the sphere, closed
up by the north pole, is a closed Jordan curve of `S²`. -/
def IsUnboundedJordanCurve (C : Set Plane) : Prop :=
  IsClosedJordanCurve (sphereCompletion C)

/-- Following the convention of Klein–Langetepe–Nilforoushan (2009) (stated after
Theorem 4), a *Jordan curve* is either a homeomorphic image of the circle or a homeomorphic
image of a line bisecting the plane. -/
def IsJordanCurve (C : Set Plane) : Prop :=
  IsClosedJordanCurve C ∨ IsUnboundedJordanCurve C

/-- `IsProperLineParam γ C` : the map `γ : ℝ → ℝ²` is a *proper parametrization* of the
curve `C`, i.e. a proper continuous injection of the line onto `C`.

This is the form in which unbounded bisecting curves are used in
Klein–Langetepe–Nilforoushan (2009): "points consecutively visited by `C`" means points
`γ t₁, …, γ t₄` with `t₁ < t₂ < t₃ < t₄`. -/
def IsProperLineParam (γ : ℝ → Plane) (C : Set Plane) : Prop :=
  Continuous γ ∧ Function.Injective γ ∧ range γ = C ∧
    ∀ K : Set Plane, IsCompact K → IsCompact (γ ⁻¹' K)

/-- A homeomorphism of the real line onto the open unit interval, used to transport a
parametrization of a closed Jordan curve of the sphere punctured at the north pole into a
parametrization of the corresponding unbounded curve of the plane. -/
def lineHomeoIoo : ℝ ≃ₜ Ioo (0 : ℝ) 1 :=
  (Homeomorph.unitBall (E := ℝ)).trans
    ((Homeomorph.setCongr
        (by rw [Real.ball_eq_Ioo]; norm_num : Metric.ball (0 : ℝ) 1 = Ioo (-1) 1)).trans
      (((affineHomeomorph (1/2 : ℝ) (1/2) (by norm_num)).image (Ioo (-1) 1)).trans
        (Homeomorph.setCongr (by rw [affineHomeomorph_image_Ioo] <;> norm_num))))

/-- **The bridge between axiom `A₁` and the parametrizations used in the proofs.**

A curve `C` of the plane whose stereographic image closes up to a closed Jordan curve
through the north pole (axiom `A₁` of Definition 1 of Klein–Langetepe–Nilforoushan (2009))
is a properly embedded line: it admits a proper continuous injective parametrization
`ℝ → ℝ²`.

Indeed, parametrize the closed Jordan curve on the sphere starting at the north pole; the
parameter interval `(0,1)` is then mapped homeomorphically onto `C` by the stereographic
projection, and properness follows because the parameter set of a compact subset of `C` is a
closed subset of `[0,1]` avoiding the two endpoints. -/
theorem IsUnboundedJordanCurve.exists_properParam {C : Set Plane}
    (h : IsUnboundedJordanCurve C) : ∃ γ : ℝ → Plane, IsProperLineParam γ C := by
  have hN : northPole ∈ sphereCompletion C := Or.inr rfl
  obtain ⟨σ, hcont, hinj, hclosed, himg, hσ0⟩ := h.exists_param_at hN
  -- on the open interval, the curve avoids the north pole
  have hne : ∀ s ∈ Ioo (0 : ℝ) 1, σ s ≠ northPole := by
    intro s hs hcon
    have : s = 0 := hinj ⟨le_of_lt hs.1, hs.2⟩ ⟨le_refl 0, one_pos⟩ (by rw [hcon, hσ0])
    exact absurd this (ne_of_gt hs.1)
  -- the image of the open interval is the stereographic image of `C`
  have himgIoo : σ '' Ioo 0 1 = stereo.symm '' C := by
    apply Subset.antisymm
    · rintro y ⟨s, hs, rfl⟩
      have hy : σ s ∈ sphereCompletion C := by
        rw [← himg]; exact ⟨s, ⟨le_of_lt hs.1, le_of_lt hs.2⟩, rfl⟩
      rcases hy with hy | hy
      · exact hy
      · exact absurd (mem_singleton_iff.1 hy) (hne s hs)
    · rintro y ⟨x, hx, rfl⟩
      have hy : stereo.symm x ∈ σ '' Icc 0 1 := by rw [himg]; exact Or.inl ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hsy⟩ := hy
      refine ⟨s, ⟨?_, ?_⟩, hsy⟩
      · rcases eq_or_lt_of_le hs.1 with h0 | h0
        · exact absurd (by rw [← hsy, ← h0, hσ0]) (stereo_symm_ne_northPole x).symm
        · exact h0
      · rcases eq_or_lt_of_le hs.2 with h1 | h1
        · exact absurd (by rw [← hsy, h1, ← hclosed, hσ0]) (stereo_symm_ne_northPole x).symm
        · exact h1
  set γ : ℝ → Plane := fun t => stereo (σ (lineHomeoIoo t)) with hγdef
  have hmemIoo : ∀ t : ℝ, ((lineHomeoIoo t : ℝ)) ∈ Ioo (0 : ℝ) 1 := fun t => (lineHomeoIoo t).2
  have hcontIoo : Continuous fun t : ℝ => σ (lineHomeoIoo t) :=
    hcont.comp_continuous (by fun_prop)
      (fun t => ⟨le_of_lt (hmemIoo t).1, le_of_lt (hmemIoo t).2⟩)
  have hcontγ : Continuous γ := by
    refine stereo.continuousOn_toFun.comp_continuous hcontIoo fun t => ?_
    rw [stereo_source]
    exact hne _ (hmemIoo t)
  refine ⟨γ, hcontγ, ?_, ?_, ?_⟩
  · -- injectivity
    intro a b hab
    have h1 : σ (lineHomeoIoo a) = σ (lineHomeoIoo b) := by
      have ha := hne _ (hmemIoo a)
      have hb := hne _ (hmemIoo b)
      have := congrArg stereo.symm hab
      rwa [stereo_symm_stereo ha, stereo_symm_stereo hb] at this
    have h2 : ((lineHomeoIoo a : ℝ)) = ((lineHomeoIoo b : ℝ)) :=
      hinj ⟨le_of_lt (hmemIoo a).1, (hmemIoo a).2⟩ ⟨le_of_lt (hmemIoo b).1, (hmemIoo b).2⟩ h1
    exact lineHomeoIoo.injective (Subtype.ext h2)
  · -- the range is `C`
    apply Subset.antisymm
    · rintro y ⟨t, rfl⟩
      have : σ (lineHomeoIoo t) ∈ stereo.symm '' C := by
        rw [← himgIoo]; exact ⟨_, hmemIoo t, rfl⟩
      obtain ⟨x, hx, hxy⟩ := this
      have : γ t = x := by rw [hγdef]; simp only; rw [← hxy, stereo_stereo_symm]
      rwa [this]
    · intro x hx
      have : stereo.symm x ∈ σ '' Ioo 0 1 := by rw [himgIoo]; exact ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hsx⟩ := this
      refine ⟨lineHomeoIoo.symm ⟨s, hs⟩, ?_⟩
      rw [hγdef]
      simp only [Homeomorph.apply_symm_apply]
      rw [hsx, stereo_stereo_symm]
  · -- properness
    intro K hK
    have hKS : IsCompact (stereo.symm '' K) := hK.image continuous_stereo_symm
    -- the parameter set of `K`, inside `[0,1]`
    set T : Set ℝ := {s ∈ Icc (0 : ℝ) 1 | σ s ∈ stereo.symm '' K} with hTdef
    have hTsub : T ⊆ Ioo (0 : ℝ) 1 := by
      rintro s ⟨hs, hsK⟩
      obtain ⟨x, -, hx⟩ := hsK
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hs.1 with h0 | h0
        · exact absurd (show stereo.symm x = northPole by rw [hx, ← h0, hσ0])
            (stereo_symm_ne_northPole x)
        · exact h0
      · rcases eq_or_lt_of_le hs.2 with h1 | h1
        · exact absurd (show stereo.symm x = northPole by rw [hx, h1, ← hclosed, hσ0])
            (stereo_symm_ne_northPole x)
        · exact h1
    have hTcompact : IsCompact T := by
      rw [hTdef]
      refine (isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset ?_ (fun s hs => hs.1)
      have : {s ∈ Icc (0 : ℝ) 1 | σ s ∈ stereo.symm '' K} =
          Icc (0 : ℝ) 1 ∩ σ ⁻¹' (stereo.symm '' K) := by
        ext s; simp
      rw [this]
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc hKS.isClosed
    have hTIoo : Ioo (0 : ℝ) 1 ∩ T = T := inter_eq_right.2 hTsub
    -- transport to the line through the homeomorphism
    have hpre : γ ⁻¹' K = lineHomeoIoo ⁻¹' (Subtype.val ⁻¹' T) := by
      ext t
      constructor
      · intro ht
        refine ⟨⟨le_of_lt (hmemIoo t).1, le_of_lt (hmemIoo t).2⟩, ?_⟩
        exact ⟨γ t, ht, by
          rw [hγdef]; simp only; rw [stereo_symm_stereo (hne _ (hmemIoo t))]⟩
      · rintro ⟨-, x, hxK, hx⟩
        have : γ t = x := by
          rw [hγdef]; simp only
          rw [← hx, stereo_stereo_symm]
        rw [mem_preimage, this]; exact hxK
    rw [hpre]
    have hsub : IsCompact (Subtype.val ⁻¹' T : Set (Ioo (0 : ℝ) 1)) := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      have : Subtype.val '' (Subtype.val ⁻¹' T : Set (Ioo (0 : ℝ) 1)) = T := by
        rw [Subtype.image_preimage_coe]
        exact hTIoo
      rw [this]; exact hTcompact
    exact (Homeomorph.isCompact_preimage lineHomeoIoo).2 hsub

/-- A curve admitting a proper parametrization by the line is an unbounded subset of the
plane: the preimage of a compact set is compact, while the whole line is not. -/
theorem IsProperLineParam.not_isBounded {γ : ℝ → Plane} {C : Set Plane}
    (h : IsProperLineParam γ C) : ¬ Bornology.IsBounded C := by
  obtain ⟨-, -, hrange, hproper⟩ := h
  intro hbdd
  have hcompact : IsCompact (closure C) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure
  have huniv : γ ⁻¹' closure C = univ := by
    ext t
    simp only [mem_preimage, mem_univ, iff_true]
    exact subset_closure (hrange ▸ mem_range_self t)
  exact absurd (huniv ▸ hproper _ hcompact) (noncompact_univ ℝ)

/-- **The curves of axiom `A₁` are unbounded.**  A curve whose stereographic image closes up
to a closed Jordan curve through the north pole (axiom `A₁` of Definition 1 of
Klein–Langetepe–Nilforoushan (2009)) is an unbounded subset of the plane — this is why the
paper calls the domains it bounds "unbounded domains". -/
theorem IsUnboundedJordanCurve.not_isBounded {C : Set Plane} (h : IsUnboundedJordanCurve C) :
    ¬ Bornology.IsBounded C := by
  obtain ⟨γ, hγ⟩ := h.exists_properParam
  exact hγ.not_isBounded

end AVD
