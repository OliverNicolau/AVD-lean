import AbstractVoronoi.Jordan.Adapter

/-!
# Arc surgery

This file develops the elementary surgery on arcs of the plane that is used, in

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

in the three "Facts" of the proof of Lemma 6 and in the "plane tree" construction of
footnote 10 (the proof of Lemma 9): reversing an arc, restricting it to a subinterval,
concatenating two arcs that meet only at a common endpoint, and cutting an arc at the
first point where it meets a closed set.

These operations are combined in `AVD.exists_arc_cut`, which is the surgery step itself:
an arc issued from a point `x` outside an arc `τ` and ending on `τ` can be cut and
concatenated with a piece of `τ` so as to give an arc from `x` to the far endpoint of `τ`.
-/

noncomputable section

open Set Topology

namespace AVD

/-! ## Reversal -/

/-- The reversal of an arc. -/
def revParam (γ : ℝ → Plane) : ℝ → Plane := fun t => γ (1 - t)

/-- The reversed arc starts where the arc ends. -/
theorem revParam_zero (γ : ℝ → Plane) : revParam γ 0 = γ 1 := by simp [revParam]

/-- The reversed arc ends where the arc starts. -/
theorem revParam_one (γ : ℝ → Plane) : revParam γ 1 = γ 0 := by simp [revParam]

/-- Reversal does not change the image of an arc. -/
theorem revParam_image (γ : ℝ → Plane) : revParam γ '' Icc 0 1 = γ '' Icc 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp [revParam]⟩

/-- Reversal does not change the relative interior of an arc. -/
theorem revParam_image_Ioo (γ : ℝ → Plane) : revParam γ '' Ioo 0 1 = γ '' Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp [revParam]⟩

/-- The reversal of an arc is an arc. -/
theorem IsArc.rev {γ : ℝ → Plane} (h : IsArc γ) : IsArc (revParam γ) := by
  constructor
  · refine h.cont.comp (by fun_prop) ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · intro s hs t ht hst
    have := h.inj (show 1 - s ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
      (show 1 - t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩) hst
    linarith

/-! ## Subarcs -/

/-- The subarc from `γ a` to `γ b` starts at `γ a`. -/
theorem subarcParam_zero (γ : ℝ → Plane) (a b : ℝ) : subarcParam γ a b 0 = γ a := by
  change γ (a + (b - a) * clamp01 0) = γ a
  rw [clamp01_of_mem ⟨le_refl 0, zero_le_one⟩]
  congr 1
  ring

/-- The subarc from `γ a` to `γ b` ends at `γ b`. -/
theorem subarcParam_one (γ : ℝ → Plane) (a b : ℝ) : subarcParam γ a b 1 = γ b := by
  change γ (a + (b - a) * clamp01 1) = γ b
  rw [clamp01_of_mem ⟨zero_le_one, le_refl 1⟩]
  congr 1
  ring

/-- The relative interior of the subarc from `γ a` to `γ b` is `γ((a,b))`. -/
theorem subarcParam_image_Ioo {γ : ℝ → Plane} {a b : ℝ} (hab : a < b) :
    subarcParam γ a b '' Ioo 0 1 = γ '' Ioo a b := by
  have hne : 0 < b - a := by linarith
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hc : clamp01 s = s := clamp01_of_mem ⟨hs.1.le, hs.2.le⟩
    refine ⟨a + (b - a) * clamp01 s, ⟨?_, ?_⟩, rfl⟩
    · rw [hc]; nlinarith [hs.1]
    · rw [hc]; nlinarith [hs.2]
  · rintro ⟨u, hu, rfl⟩
    have hmem : (u - a) / (b - a) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (by linarith [hu.1]) hne, by rw [div_lt_one hne]; linarith [hu.2]⟩
    refine ⟨(u - a) / (b - a), hmem, ?_⟩
    change γ (a + (b - a) * clamp01 ((u - a) / (b - a))) = γ u
    rw [clamp01_of_mem ⟨hmem.1.le, hmem.2.le⟩]
    congr 1
    field_simp
    ring

/-- A subarc of an arc, traversed from `γ a` to `γ b` with `a < b`, is again an arc. -/
theorem IsArc.subarc {γ : ℝ → Plane} (h : IsArc γ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) : IsArc (subarcParam γ a b) :=
  ⟨(continuous_subarcParam h ha hab.le hb).continuousOn, subarcParam_injOn h ha hab hb⟩

/-! ## Concatenation -/

/-- The concatenation of two arcs: `γ` traversed on `[0,1/2]`, then `δ` on `[1/2,1]`. -/
def concatParam (γ δ : ℝ → Plane) : ℝ → Plane :=
  Set.piecewise (Iic (1/2 : ℝ)) (fun t => γ (2 * t)) (fun t => δ (2 * t - 1))

/-- On `[0,1/2]` the concatenation of two arcs traverses the first one. -/
theorem concatParam_of_le {γ δ : ℝ → Plane} {t : ℝ} (ht : t ≤ 1 / 2) :
    concatParam γ δ t = γ (2 * t) :=
  Set.piecewise_eq_of_mem _ _ _ (by simpa using ht)

/-- On `(1/2,1]` the concatenation of two arcs traverses the second one. -/
theorem concatParam_of_gt {γ δ : ℝ → Plane} {t : ℝ} (ht : ¬ t ≤ 1/2) :
    concatParam γ δ t = δ (2 * t - 1) :=
  Set.piecewise_eq_of_notMem _ _ _ (by simpa using ht)

/-- The concatenation of two arcs starts where the first one starts. -/
theorem concatParam_zero (γ δ : ℝ → Plane) : concatParam γ δ 0 = γ 0 := by
  rw [concatParam_of_le (by norm_num)]
  norm_num

/-- The concatenation of two arcs ends where the second one ends. -/
theorem concatParam_one (γ δ : ℝ → Plane) : concatParam γ δ 1 = δ 1 := by
  rw [concatParam_of_gt (by norm_num)]
  norm_num

/-- The image of the concatenation of two arcs meeting at `γ 1 = δ 0` is the union of
their images. -/
theorem concatParam_image {γ δ : ℝ → Plane} (hmid : γ 1 = δ 0) :
    concatParam γ δ '' Icc 0 1 = γ '' Icc 0 1 ∪ δ '' Icc 0 1 := by
  apply Subset.antisymm
  · rintro x ⟨t, ht, rfl⟩
    rcases le_or_gt t (1/2) with h | h
    · exact Or.inl ⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, (concatParam_of_le h).symm⟩
    · exact Or.inr ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩,
        (concatParam_of_gt (not_le.2 h)).symm⟩
  · rintro x (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rw [concatParam_of_le (by linarith [ht.2])]
      congr 1
      ring
    · refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · have h12 : ((t : ℝ) + 1) / 2 ≤ 1 / 2 := by rw [← h0]; norm_num
        rw [concatParam_of_le h12, ← h0]
        norm_num
        exact hmid
      · rw [concatParam_of_gt (by intro hc; linarith)]
        congr 1
        ring

/-- The concatenation of two arcs meeting only at the common endpoint is an arc. -/
theorem IsArc.concat {γ δ : ℝ → Plane} (hγ : IsArc γ) (hδ : IsArc δ) (hmid : γ 1 = δ 0)
    (hint : γ '' Icc 0 1 ∩ δ '' Icc 0 1 ⊆ {γ 1}) : IsArc (concatParam γ δ) := by
  constructor
  · refine ContinuousOn.piecewise ?_ ?_ ?_
    · intro t ht
      have ht' : t = 1/2 := by simpa [frontier_Iic] using ht.2
      subst ht'
      norm_num [hmid]
    · refine hγ.cont.comp (by fun_prop) ?_
      rintro t ⟨ht, ht'⟩
      rw [closure_Iic] at ht'
      exact ⟨by linarith [ht.1], by linarith [mem_Iic.1 ht']⟩
    · refine hδ.cont.comp (by fun_prop) ?_
      rintro t ⟨ht, ht'⟩
      rw [compl_Iic, closure_Ioi] at ht'
      exact ⟨by linarith [mem_Ici.1 ht'], by linarith [ht.2]⟩
  · intro s hs t ht hst
    rcases le_or_gt s (1/2) with hs2 | hs2 <;> rcases le_or_gt t (1/2) with ht2 | ht2
    · rw [concatParam_of_le hs2, concatParam_of_le ht2] at hst
      have := hγ.inj ⟨by linarith [hs.1], by linarith⟩ ⟨by linarith [ht.1], by linarith⟩ hst
      linarith
    · rw [concatParam_of_le hs2, concatParam_of_gt (not_le.2 ht2)] at hst
      -- the common point is `γ 1 = δ 0`
      have hmem : γ (2 * s) ∈ γ '' Icc 0 1 ∩ δ '' Icc 0 1 :=
        ⟨⟨2 * s, ⟨by linarith [hs.1], by linarith⟩, rfl⟩,
          ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, hst.symm⟩⟩
      have h1 : γ (2 * s) = γ 1 := hint hmem
      have hs1 : 2 * s = 1 := hγ.inj ⟨by linarith [hs.1], by linarith⟩
        ⟨zero_le_one, le_refl 1⟩ h1
      have hmem' : δ (2 * t - 1) ∈ γ '' Icc 0 1 ∩ δ '' Icc 0 1 :=
        ⟨⟨2 * s, ⟨by linarith [hs.1], by linarith⟩, hst⟩,
          ⟨2 * t - 1, ⟨by linarith, by linarith [ht.2]⟩, rfl⟩⟩
      have h2 : δ (2 * t - 1) = δ 0 := by rw [hint hmem', hmid]
      have ht1 : 2 * t - 1 = 0 := hδ.inj ⟨by linarith, by linarith [ht.2]⟩
        ⟨le_refl 0, zero_le_one⟩ h2
      linarith
    · rw [concatParam_of_gt (not_le.2 hs2), concatParam_of_le ht2] at hst
      have hmem : γ (2 * t) ∈ γ '' Icc 0 1 ∩ δ '' Icc 0 1 :=
        ⟨⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, rfl⟩,
          ⟨2 * s - 1, ⟨by linarith, by linarith [hs.2]⟩, hst⟩⟩
      have h1 : γ (2 * t) = γ 1 := hint hmem
      have ht1 : 2 * t = 1 := hγ.inj ⟨by linarith [ht.1], by linarith⟩
        ⟨zero_le_one, le_refl 1⟩ h1
      have hmem' : δ (2 * s - 1) ∈ γ '' Icc 0 1 ∩ δ '' Icc 0 1 :=
        ⟨⟨2 * t, ⟨by linarith [ht.1], by linarith⟩, hst.symm⟩,
          ⟨2 * s - 1, ⟨by linarith, by linarith [hs.2]⟩, rfl⟩⟩
      have h2 : δ (2 * s - 1) = δ 0 := by rw [hint hmem', hmid]
      have hs1 : 2 * s - 1 = 0 := hδ.inj ⟨by linarith, by linarith [hs.2]⟩
        ⟨le_refl 0, zero_le_one⟩ h2
      linarith
    · rw [concatParam_of_gt (not_le.2 hs2), concatParam_of_gt (not_le.2 ht2)] at hst
      have := hδ.inj ⟨by linarith, by linarith [hs.2]⟩ ⟨by linarith, by linarith [ht.2]⟩ hst
      linarith

/-! ## Cutting at the first intersection point -/

/-- An arc starting outside a closed set `K` and ending in `K` has a *first* point in `K`. -/
theorem exists_first_hit {γ : ℝ → Plane} (hcont : ContinuousOn γ (Icc 0 1)) {K : Set Plane}
    (hK : IsClosed K) (h0 : γ 0 ∉ K) (h1 : γ 1 ∈ K) :
    ∃ t ∈ Ioc (0 : ℝ) 1, γ t ∈ K ∧ ∀ s ∈ Ico (0 : ℝ) t, γ s ∉ K := by
  set T : Set ℝ := Icc 0 1 ∩ γ ⁻¹' K with hT
  have hTclosed : IsClosed T := hcont.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hTne : T.Nonempty := ⟨1, ⟨zero_le_one, le_refl 1⟩, h1⟩
  have hTbdd : BddBelow T := ⟨0, fun x hx => hx.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTclosed.csInf_mem hTne hTbdd
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le htT.1.1 with h | h
    · exact absurd (show γ 0 ∈ K by rw [h]; exact htT.2) h0
    · exact h
  refine ⟨t, ⟨ht0, htT.1.2⟩, htT.2, ?_⟩
  intro s hs hsK
  have : s ∈ T := ⟨⟨hs.1, le_trans hs.2.le htT.1.2⟩, hsK⟩
  exact absurd (csInf_le hTbdd this) (not_le.2 hs.2)

/-! ## The surgery step -/

/-- The image of the relative interior of an arc omits its two endpoints. -/
theorem IsArc.image_Ioo_subset_diff {γ : ℝ → Plane} (h : IsArc γ) :
    γ '' Ioo 0 1 ⊆ γ '' Icc 0 1 \ {γ 0, γ 1} := by
  rintro x ⟨t, ht, rfl⟩
  refine ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, ?_⟩
  rintro (h0 | h1)
  · have := h.inj ⟨ht.1.le, ht.2.le⟩ ⟨le_refl 0, zero_le_one⟩ h0
    linarith [ht.1]
  · have := h.inj ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_refl 1⟩ h1
    linarith [ht.2]

/-- **The surgery step.**  If an arc `σ` starts at a point `x` which does not lie on an arc
`τ` and ends on `τ`, then `x` can be joined to the endpoint `τ 1` by an arc contained in
the union of the two arcs.  (This is the cutting used in the "Facts" of the proof of
Lemma 6 of Klein–Langetepe–Nilforoushan (2009): the arc is followed until it first meets
the other one, and is then continued along it.) -/
theorem exists_arc_cut {σ τ : ℝ → Plane} (hσ : IsArc σ) (hτ : IsArc τ)
    (hx : σ 0 ∉ τ '' Icc 0 1) (hend : σ 1 ∈ τ '' Icc 0 1) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = σ 0 ∧ γ 1 = τ 1 ∧
      γ '' Icc 0 1 ⊆ σ '' Icc 0 1 ∪ τ '' Icc 0 1 := by
  classical
  -- the image of `τ` is compact, hence closed
  have hτclosed : IsClosed (τ '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hτ.cont).isClosed
  obtain ⟨t, ht, htK, hfirst⟩ := exists_first_hit hσ.cont hτclosed hx hend
  obtain ⟨u, hu, huval⟩ : ∃ u ∈ Icc (0 : ℝ) 1, τ u = σ t := htK
  -- the initial piece of `σ`, from `σ 0` to the first point on `τ`
  have hσ' : IsArc (subarcParam σ 0 t) := hσ.subarc (le_refl 0) ht.1 ht.2
  have hσ'0 : subarcParam σ 0 t 0 = σ 0 := subarcParam_zero _ _ _
  have hσ'1 : subarcParam σ 0 t 1 = σ t := subarcParam_one _ _ _
  have hσ'img : subarcParam σ 0 t '' Icc 0 1 = σ '' Icc 0 t := subarcParam_image ht.1.le
  -- the piece of `τ` from that point to its endpoint
  by_cases hu1 : u = 1
  · -- the first point met is the endpoint of `τ`
    refine ⟨subarcParam σ 0 t, hσ', hσ'0, ?_, ?_⟩
    · rw [hσ'1, ← huval, hu1]
    · rw [hσ'img]
      exact fun x hx' => Or.inl (Set.image_mono (Icc_subset_Icc (le_refl 0) ht.2) hx')
  · have hu1' : u < 1 := lt_of_le_of_ne hu.2 hu1
    have hτ' : IsArc (subarcParam τ u 1) := hτ.subarc hu.1 hu1' (le_refl 1)
    have hτ'0 : subarcParam τ u 1 0 = σ t := by rw [subarcParam_zero, huval]
    have hτ'1 : subarcParam τ u 1 1 = τ 1 := subarcParam_one _ _ _
    have hτ'img : subarcParam τ u 1 '' Icc 0 1 = τ '' Icc u 1 := subarcParam_image hu1'.le
    -- the two pieces meet only at `σ t`
    have hint : subarcParam σ 0 t '' Icc 0 1 ∩ subarcParam τ u 1 '' Icc 0 1 ⊆
        {subarcParam σ 0 t 1} := by
      rw [hσ'img, hτ'img, hσ'1]
      rintro x ⟨⟨s, hs, rfl⟩, hx2⟩
      rcases eq_or_lt_of_le hs.2 with hst | hst
      · simp [hst]
      · exfalso
        exact hfirst s ⟨hs.1, hst⟩
          (Set.image_mono (Icc_subset_Icc hu.1 (le_refl 1)) hx2)
    refine ⟨concatParam (subarcParam σ 0 t) (subarcParam τ u 1),
      hσ'.concat hτ' (by rw [hσ'1, hτ'0]) hint, ?_, ?_, ?_⟩
    · rw [concatParam_zero, hσ'0]
    · rw [concatParam_one, hτ'1]
    · rw [concatParam_image (by rw [hσ'1, hτ'0]), hσ'img, hτ'img]
      exact union_subset_union (Set.image_mono (Icc_subset_Icc (le_refl 0) ht.2))
        (Set.image_mono (Icc_subset_Icc hu.1 (le_refl 1)))

/-- If the image of an arc from `a` to `b` is contained in `R` together with the two
endpoints, then its relative interior is contained in `R`. -/
theorem IsArc.image_Ioo_subset_of_image_subset {γ : ℝ → Plane} (h : IsArc γ)
    {R : Set Plane} {a b : Plane} (h0 : γ 0 = a) (h1 : γ 1 = b)
    (hsub : γ '' Icc 0 1 ⊆ R ∪ {a, b}) : γ '' Ioo 0 1 ⊆ R := by
  intro x hx
  obtain ⟨hximg, hxne⟩ := h.image_Ioo_subset_diff hx
  rcases hsub hximg with hxR | hxab
  · exact hxR
  · exfalso
    rcases hxab with rfl | rfl
    · exact hxne (Or.inl h0.symm)
    · exact hxne (Or.inr h1.symm)

/-- The image of an access arc is contained in the set together with the accessed point. -/
theorem image_Icc_subset_of_image_Ico {γ : ℝ → Plane} {R : Set Plane}
    (hsub : γ '' Ico 0 1 ⊆ R) : γ '' Icc 0 1 ⊆ R ∪ {γ 1} := by
  rintro x ⟨t, ht, rfl⟩
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · exact Or.inr (by simp [h1])
  · exact Or.inl (hsub ⟨t, ⟨ht.1, h1⟩, rfl⟩)

/-- Every point of an open set is accessible from it (by a small segment). -/
theorem accessible_of_mem_open {R : Set Plane} (hopen : IsOpen R) {x : Plane} (hx : x ∈ R) :
    AccessibleFrom R x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x hx
  set e : Plane := EuclideanSpace.single 0 (r / 2) with hedef
  have hnorm : ‖e‖ = r / 2 := by
    rw [hedef, PiLp.norm_single 2 (fun _ => ℝ) 0 (r / 2)]
    exact abs_of_pos (by linarith)
  refine ⟨fun t => x + (1 - t) • e, ⟨by fun_prop, ?_⟩, by simp, ?_⟩
  · intro s _ t _ hst
    have h : (1 - s) • e = (1 - t) • e := by
      simpa using congrArg (fun y => y - x) hst
    have hne : e ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnorm
      linarith
    have := sub_eq_zero.2 h
    rw [← sub_smul] at this
    rcases smul_eq_zero.1 this with h1 | h1
    · linarith [sub_eq_zero.1 (by linarith [h1] : (1 - s) - (1 - t) = 0)]
    · exact absurd h1 hne
  · rintro y ⟨t, ht, rfl⟩
    refine hball ?_
    have : ‖(1 - t) • e‖ = (1 - t) * (r / 2) := by
      rw [norm_smul, hnorm, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    simp only [Metric.mem_ball, dist_eq_norm]
    have h : x + (1 - t) • e - x = (1 - t) • e := by abel
    rw [h, this]
    nlinarith [ht.1, ht.2]

end AVD
