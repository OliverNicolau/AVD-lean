import AbstractVoronoi.Jordan.ArcFacts
import AbstractVoronoi.Jordan.Schoenflies
import AbstractVoronoi.Jordan.Backend

/-!
# Completing an arc to a closed Jordan curve

The degree condition used by the Euler count in the proof of **Theorem 10** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

is a statement about how a small piece of the diagram separates a neighbourhood of a vertex.
Near a vertex at which only two edges end, that piece is an **arc** through the vertex, made
of one branch of each of the two bisecting curves carrying the two edges.  The lemma
`AVD.faces_at_ncard_le_two_of_local_subset_jordan` counts the faces meeting a point at which
the set lies on a *Jordan curve*, so what is needed is to put that arc on a closed Jordan
curve.

This file does that.  The main result is

* `AVD.exists_closedJordanCurve_extend` — an arc `k` which can be *continued* at both of its
  endpoints, by two arcs `p`, `q` that leave `k` immediately and are disjoint from each
  other, lies on a closed Jordan curve.  The completing arc is obtained from the
  non-separation theorem for arcs (`AVD.exists_arc_avoiding_arc`: two points off an arc can
  be joined by an arc avoiding it), followed by the surgery step `AVD.exists_arc_cut` at both
  ends;
* `AVD.exists_closedJordanCurve_two_branches` — its form for two branches
  `γ₁([0,d₁])`, `γ₂([0,d₂])` of two properly embedded lines issued from a common point
  `γ₁ 0 = γ₂ 0`, which is how it is applied at a Voronoi vertex.
-/

noncomputable section

open Set Topology

namespace AVD

/-! ## Affine pieces of a properly embedded line -/

/-- The piece of the curve `γ` running from `γ a` to `γ b`, parametrized affinely by
`[0,1]`. -/
def lineArc (γ : ℝ → Plane) (a b : ℝ) : ℝ → Plane := fun t => γ (a + (b - a) * t)

/-- The piece of `γ` from `γ a` to `γ b` starts at `γ a`. -/
theorem lineArc_zero (γ : ℝ → Plane) (a b : ℝ) : lineArc γ a b 0 = γ a := by
  simp [lineArc]

/-- The piece of `γ` from `γ a` to `γ b` ends at `γ b`. -/
theorem lineArc_one (γ : ℝ → Plane) (a b : ℝ) : lineArc γ a b 1 = γ b := by
  simp [lineArc]

/-- The affine parametrization of `[a,b]` by `[0,1]`. -/
theorem affine_image_Icc {a b : ℝ} (hab : a ≤ b) :
    (fun t : ℝ => a + (b - a) * t) '' Icc 0 1 = Icc a b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  · intro hx
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact ⟨0, ⟨le_refl 0, zero_le_one⟩, by simp [le_antisymm hx.2 hx.1]⟩
    · have hne : 0 < b - a := by linarith
      refine ⟨(x - a) / (b - a), ⟨div_nonneg (by linarith [hx.1]) hne.le,
        by rw [div_le_one hne]; linarith [hx.2]⟩, ?_⟩
      field_simp
      ring

/-- The affine parametrization of `(a,b]` by `(0,1]`. -/
theorem affine_image_Ioc {a b : ℝ} (hab : a < b) :
    (fun t : ℝ => a + (b - a) * t) '' Ioc 0 1 = Ioc a b := by
  have hne : 0 < b - a := by linarith
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  · intro hx
    refine ⟨(x - a) / (b - a), ⟨div_pos (by linarith [hx.1]) hne,
      by rw [div_le_one hne]; linarith [hx.2]⟩, ?_⟩
    field_simp
    ring

/-- The image of the piece of `γ` from `γ a` to `γ b` is `γ([a,b])`. -/
theorem lineArc_image_Icc (γ : ℝ → Plane) {a b : ℝ} (hab : a ≤ b) :
    lineArc γ a b '' Icc 0 1 = γ '' Icc a b := by
  rw [show lineArc γ a b = γ ∘ (fun t : ℝ => a + (b - a) * t) from rfl, image_comp,
    affine_image_Icc hab]

/-- The image of the piece of `γ` from `γ a` to `γ b`, minus its initial point, is
`γ((a,b])`. -/
theorem lineArc_image_Ioc (γ : ℝ → Plane) {a b : ℝ} (hab : a < b) :
    lineArc γ a b '' Ioc 0 1 = γ '' Ioc a b := by
  rw [show lineArc γ a b = γ ∘ (fun t : ℝ => a + (b - a) * t) from rfl, image_comp,
    affine_image_Ioc hab]

/-- A piece of a continuous injective curve, affinely parametrized, is an arc. -/
theorem isArc_lineArc {γ : ℝ → Plane} (hc : Continuous γ) (hi : Function.Injective γ)
    {a b : ℝ} (hab : a < b) : IsArc (lineArc γ a b) := by
  refine ⟨(hc.comp (by fun_prop)).continuousOn, fun s _ t _ hst => ?_⟩
  have h := hi hst
  have hne : b - a ≠ 0 := by linarith
  exact mul_left_cancel₀ hne (by linarith)

/-! ## Completing an arc to a closed Jordan curve -/

/-- **An arc that can be continued at both of its ends lies on a closed Jordan curve.**

Let `k` be an arc, and let `p`, `q` be two arcs issued from its two endpoints
(`p 0 = k 0`, `q 0 = k 1`) which leave `k` immediately (the images of `(0,1]` under `p` and
`q` miss `k`) and are disjoint from each other.  Then there is a closed Jordan curve
containing `k`.

The two far endpoints `p 1` and `q 1` lie off `k`, so the non-separation theorem for arcs
(`AVD.exists_arc_avoiding_arc`) joins them by an arc `τ` avoiding `k` altogether; cutting
`p` and then `q` at their first meeting point with what has been built so far
(`AVD.exists_arc_cut`) turns `p ∪ τ ∪ q` into a single arc from `k 0` to `k 1` which meets
`k` only at those two endpoints, and the two arcs together close up into a Jordan curve
(`AVD.isClosedJordanCurve_of_arcs`).

This is the ingredient which, at a Voronoi vertex where only two edges end, puts the two
branches of the diagram on a Jordan curve, so that the local count of faces
`AVD.faces_at_ncard_le_two_of_local_subset_jordan` can be applied. -/
theorem exists_closedJordanCurve_extend {k p q : ℝ → Plane} (hk : IsArc k) (hp : IsArc p)
    (hq : IsArc q) (hp0 : p 0 = k 0) (hq0 : q 0 = k 1)
    (hpk : Disjoint (p '' Ioc 0 1) (k '' Icc 0 1))
    (hqk : Disjoint (q '' Ioc 0 1) (k '' Icc 0 1))
    (hpq : Disjoint (p '' Icc 0 1) (q '' Icc 0 1)) :
    ∃ C : Set Plane, IsClosedJordanCurve C ∧ k '' Icc 0 1 ⊆ C := by
  have hmem01 : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_refl 1⟩
  -- the arc `k`, as a set-level arc of the backend
  have hkarc : Backend.IsArc (k '' Icc 0 1) := ⟨k, hk.cont, hk.inj, rfl⟩
  -- the two far endpoints lie off `k`
  have hx1 : p 1 ∉ k '' Icc 0 1 :=
    fun h => (Set.disjoint_left.1 hpk) ⟨1, hmem01, rfl⟩ h
  have hx2 : q 1 ∉ k '' Icc 0 1 :=
    fun h => (Set.disjoint_left.1 hqk) ⟨1, hmem01, rfl⟩ h
  have hxne : p 1 ≠ q 1 := by
    intro h
    exact (Set.disjoint_left.1 hpq) ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
      ⟨1, ⟨zero_le_one, le_refl 1⟩, h.symm⟩
  -- an arc joining them off `k`
  obtain ⟨τ, hτ, hτ0, hτ1, hτdisj⟩ := exists_arc_avoiding_arc hkarc hx1 hx2 hxne
  -- the piece of `p` followed by a piece of `τ`
  have hp0τ : p 0 ∉ τ '' Icc 0 1 := by
    intro h
    exact (Set.disjoint_left.1 hτdisj) (hp0 ▸ ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩) h
  have hp1τ : p 1 ∈ τ '' Icc 0 1 := ⟨0, ⟨le_refl 0, zero_le_one⟩, hτ0⟩
  obtain ⟨ω, hω, hω0, hω1, hωsub⟩ := exists_arc_cut hp hτ hp0τ hp1τ
  -- `p` meets `k` only at `k 0`
  have hpIcc : p '' Icc 0 1 ⊆ {p 0} ∪ p '' Ioc 0 1 := by
    rintro x ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Or.inl (by simp [← h])
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  -- the piece of `q` followed by the reversal of what has been built
  have hq0ω : q 0 ∉ revParam ω '' Icc 0 1 := by
    rw [revParam_image]
    intro h
    rcases hωsub h with hx | hx
    · rcases hpIcc hx with hx' | hx'
      · rw [Set.mem_singleton_iff, hp0] at hx'
        have := hk.inj (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_refl 1⟩)
          (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_refl 0, zero_le_one⟩) (by rw [← hq0, hx'])
        norm_num at this
      · exact (Set.disjoint_left.1 hpk) hx' (hq0 ▸ ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩)
    · exact (Set.disjoint_left.1 hτdisj) (hq0 ▸ ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩) hx
  have hq1ω : q 1 ∈ revParam ω '' Icc 0 1 := by
    rw [revParam_image]
    exact ⟨1, ⟨zero_le_one, le_refl 1⟩, by rw [hω1, hτ1]⟩
  obtain ⟨ξ, hξ, hξ0, hξ1, hξsub⟩ := exists_arc_cut hq hω.rev hq0ω hq1ω
  -- the completing arc, from `k 0` to `k 1`
  set σ : ℝ → Plane := revParam ξ with hσdef
  have hσarc : IsArc σ := hξ.rev
  have hσ0 : σ 0 = k 0 := by
    rw [hσdef, revParam_zero, hξ1, revParam_one, hω0, hp0]
  have hσ1 : σ 1 = k 1 := by
    rw [hσdef, revParam_one, hξ0, hq0]
  -- its image avoids `k` except at the two endpoints
  have hσsub : σ '' Icc 0 1 ⊆ (p '' Icc 0 1 ∪ q '' Icc 0 1) ∪ τ '' Icc 0 1 := by
    rw [hσdef, revParam_image]
    intro x hx
    rcases hξsub hx with hx' | hx'
    · exact Or.inl (Or.inr hx')
    · rw [revParam_image] at hx'
      rcases hωsub hx' with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  have hPk : ((p '' Icc 0 1 ∪ q '' Icc 0 1) ∪ τ '' Icc 0 1) ∩ k '' Icc 0 1 ⊆ {k 0, k 1} := by
    rintro x ⟨hxP, hxk⟩
    rcases hxP with (hx | hx) | hx
    · rcases hpIcc hx with hx' | hx'
      · rw [Set.mem_singleton_iff, hp0] at hx'
        exact Or.inl hx'
      · exact absurd hxk ((Set.disjoint_left.1 hpk) hx')
    · have hqIcc : q '' Icc 0 1 ⊆ {q 0} ∪ q '' Ioc 0 1 := by
        rintro y ⟨t, ht, rfl⟩
        rcases eq_or_lt_of_le ht.1 with h | h
        · exact Or.inl (by simp [← h])
        · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
      rcases hqIcc hx with hx' | hx'
      · rw [Set.mem_singleton_iff, hq0] at hx'
        exact Or.inr hx'
      · exact absurd hxk ((Set.disjoint_left.1 hqk) hx')
    · exact absurd hx ((Set.disjoint_left.1 hτdisj) hxk)
  have hdisjIoo : Disjoint (k '' Ioo 0 1) (σ '' Ioo 0 1) := by
    refine Set.disjoint_right.2 fun x hx hxk => ?_
    obtain ⟨hxIcc, hxne⟩ := hσarc.image_Ioo_subset_diff hx
    have hxk' : x ∈ k '' Icc 0 1 := image_mono Ioo_subset_Icc_self hxk
    have := hPk ⟨hσsub hxIcc, hxk'⟩
    rcases this with h | h
    · exact hxne (Or.inl (by rw [h, hσ0]))
    · exact hxne (Or.inr (by simp [Set.mem_singleton_iff.1 h, hσ1]))
  exact ⟨k '' Icc 0 1 ∪ σ '' Icc 0 1,
    isClosedJordanCurve_of_arcs hk hσarc hσ0.symm hσ1.symm hdisjIoo, subset_union_left⟩

/-- **Two branches issued from a common point lie on a closed Jordan curve.**

Let `γ₁`, `γ₂` be proper parametrizations of two properly embedded lines of the plane with
`γ₁ 0 = γ₂ 0`, and suppose the two branches `γ₁((0,c₁])` and `γ₂((0,c₂])` are disjoint.
Then, for `0 < dᵢ < cᵢ`, the union of the two shorter branches
`γ₁([0,d₁]) ∪ γ₂([0,d₂])` — an arc through the common point — lies on a closed Jordan curve.

This is `AVD.exists_closedJordanCurve_extend` applied to the arc formed by the two shorter
branches, continued by the two remaining pieces `γᵢ([dᵢ,cᵢ])`.  It is the form in which the
result is used at a Voronoi vertex where only two edges end. -/
theorem exists_closedJordanCurve_two_branches {γ₁ γ₂ : ℝ → Plane} {L₁ L₂ : Set Plane}
    (h₁ : IsProperLineParam γ₁ L₁) (h₂ : IsProperLineParam γ₂ L₂) (hz : γ₁ 0 = γ₂ 0)
    {d₁ c₁ d₂ c₂ : ℝ} (hd₁ : 0 < d₁) (hdc₁ : d₁ < c₁) (hd₂ : 0 < d₂) (hdc₂ : d₂ < c₂)
    (hdisj : Disjoint (γ₁ '' Ioc 0 c₁) (γ₂ '' Ioc 0 c₂)) :
    ∃ C : Set Plane, IsClosedJordanCurve C ∧ γ₁ '' Icc 0 d₁ ∪ γ₂ '' Icc 0 d₂ ⊆ C := by
  obtain ⟨hc1, hi1, -, -⟩ := h₁
  obtain ⟨hc2, hi2, -, -⟩ := h₂
  -- the two branches, as arcs meeting only at the common point
  set k₁ : ℝ → Plane := revParam (lineArc γ₁ 0 d₁) with hk₁def
  set k₂ : ℝ → Plane := lineArc γ₂ 0 d₂ with hk₂def
  have hk₁arc : IsArc k₁ := (isArc_lineArc hc1 hi1 hd₁).rev
  have hk₂arc : IsArc k₂ := isArc_lineArc hc2 hi2 hd₂
  have hk₁img : k₁ '' Icc 0 1 = γ₁ '' Icc 0 d₁ := by
    rw [hk₁def, revParam_image, lineArc_image_Icc _ hd₁.le]
  have hk₂img : k₂ '' Icc 0 1 = γ₂ '' Icc 0 d₂ := by
    rw [hk₂def, lineArc_image_Icc _ hd₂.le]
  have hk₁0 : k₁ 0 = γ₁ d₁ := by rw [hk₁def, revParam_zero, lineArc_one]
  have hk₁1 : k₁ 1 = γ₁ 0 := by rw [hk₁def, revParam_one, lineArc_zero]
  have hk₂0 : k₂ 0 = γ₂ 0 := by rw [hk₂def, lineArc_zero]
  have hk₂1 : k₂ 1 = γ₂ d₂ := by rw [hk₂def, lineArc_one]
  -- the two branches meet only at the common point
  have hbranch_disj : γ₁ '' Ioc 0 d₁ ∩ γ₂ '' Ioc 0 d₂ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x ⟨hx1, hx2⟩ => ?_
    exact (Set.disjoint_left.1 hdisj) (image_mono (Ioc_subset_Ioc_right hdc₁.le) hx1)
      (image_mono (Ioc_subset_Ioc_right hdc₂.le) hx2)
  have hIccIoc : ∀ (γ : ℝ → Plane) (d : ℝ), γ '' Icc 0 d ⊆ {γ 0} ∪ γ '' Ioc 0 d := by
    rintro γ d x ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Or.inl (by simp [← h])
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  have hkint : k₁ '' Icc 0 1 ∩ k₂ '' Icc 0 1 ⊆ {k₁ 1} := by
    rw [hk₁img, hk₂img, hk₁1]
    rintro x ⟨hx1, hx2⟩
    rcases hIccIoc γ₁ d₁ hx1 with h1 | h1
    · exact h1
    · rcases hIccIoc γ₂ d₂ hx2 with h2 | h2
      · rw [Set.mem_singleton_iff, ← hz] at h2
        exact h2
      · exact absurd (Set.mem_inter h1 h2) (by rw [hbranch_disj]; exact notMem_empty x)
  -- the arc through the common point
  set k : ℝ → Plane := concatParam k₁ k₂ with hkdef
  have hmid : k₁ 1 = k₂ 0 := by rw [hk₁1, hk₂0, hz]
  have hkarc : IsArc k := hk₁arc.concat hk₂arc hmid hkint
  have hkimg : k '' Icc 0 1 = γ₁ '' Icc 0 d₁ ∪ γ₂ '' Icc 0 d₂ := by
    rw [hkdef, concatParam_image hmid, hk₁img, hk₂img]
  have hk0 : k 0 = γ₁ d₁ := by rw [hkdef, concatParam_zero, hk₁0]
  have hk1 : k 1 = γ₂ d₂ := by rw [hkdef, concatParam_one, hk₂1]
  -- the two continuations
  set p : ℝ → Plane := lineArc γ₁ d₁ c₁ with hpdef
  set q : ℝ → Plane := lineArc γ₂ d₂ c₂ with hqdef
  have hparc : IsArc p := isArc_lineArc hc1 hi1 hdc₁
  have hqarc : IsArc q := isArc_lineArc hc2 hi2 hdc₂
  have hpimg : p '' Icc 0 1 = γ₁ '' Icc d₁ c₁ := lineArc_image_Icc _ hdc₁.le
  have hqimg : q '' Icc 0 1 = γ₂ '' Icc d₂ c₂ := lineArc_image_Icc _ hdc₂.le
  have hpIoc : p '' Ioc 0 1 = γ₁ '' Ioc d₁ c₁ := lineArc_image_Ioc _ hdc₁
  have hqIoc : q '' Ioc 0 1 = γ₂ '' Ioc d₂ c₂ := lineArc_image_Ioc _ hdc₂
  have hp0 : p 0 = k 0 := by rw [hpdef, lineArc_zero, hk0]
  have hq0 : q 0 = k 1 := by rw [hqdef, lineArc_zero, hk1]
  -- the continuations leave the arc at once
  have hpk : Disjoint (p '' Ioc 0 1) (k '' Icc 0 1) := by
    rw [hpIoc, hkimg]
    refine Set.disjoint_left.2 ?_
    rintro x ⟨t, ht, rfl⟩ (hx | hx)
    · obtain ⟨s, hs, hsx⟩ := hx
      have := hi1 hsx
      linarith [ht.1, hs.2]
    · rcases hIccIoc γ₂ d₂ hx with h | h
      · rw [Set.mem_singleton_iff, ← hz] at h
        have := hi1 h
        linarith [ht.1]
      · exact (Set.disjoint_left.1 hdisj)
          ⟨t, ⟨lt_trans hd₁ ht.1, ht.2⟩, rfl⟩ (image_mono (Ioc_subset_Ioc_right hdc₂.le) h)
  have hqk : Disjoint (q '' Ioc 0 1) (k '' Icc 0 1) := by
    rw [hqIoc, hkimg]
    refine Set.disjoint_left.2 ?_
    rintro x ⟨t, ht, rfl⟩ (hx | hx)
    · rcases hIccIoc γ₁ d₁ hx with h | h
      · rw [Set.mem_singleton_iff, hz] at h
        have := hi2 h
        linarith [ht.1]
      · exact (Set.disjoint_left.1 hdisj) (image_mono (Ioc_subset_Ioc_right hdc₁.le) h)
          ⟨t, ⟨lt_trans hd₂ ht.1, ht.2⟩, rfl⟩
    · obtain ⟨s, hs, hsx⟩ := hx
      have := hi2 hsx
      linarith [ht.1, hs.2]
  have hpq : Disjoint (p '' Icc 0 1) (q '' Icc 0 1) := by
    rw [hpimg, hqimg]
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, hts⟩ := hx'
    exact (Set.disjoint_left.1 hdisj) ⟨s, ⟨lt_of_lt_of_le hd₁ hs.1, hs.2⟩, rfl⟩
      ⟨t, ⟨lt_of_lt_of_le hd₂ ht.1, ht.2⟩, hts⟩
  obtain ⟨C, hC, hsub⟩ := exists_closedJordanCurve_extend hkarc hparc hqarc hp0 hq0 hpk hqk hpq
  exact ⟨C, hC, by rw [← hkimg]; exact hsub⟩

end AVD
