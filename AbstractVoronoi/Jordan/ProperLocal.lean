import AbstractVoronoi.Jordan.Sphere

/-!
# Properly embedded lines seen near one of their points

A *proper parametrization* `γ : ℝ → ℝ²` of an unbounded curve (`AVD.IsProperLineParam`, the
form in which axiom `A₁` of Definition 1 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

is used from Lemma 6 on) is continuous, injective, onto the curve, and proper: the preimage
of a compact set is compact.

Two consequences of properness are proved here, both of them about the local picture of the
curve at one of its points:

* `AVD.IsProperLineParam.affine` — reparametrizing by an affine bijection `t ↦ c + u·t` of the
  line, `u ≠ 0`, gives again a proper parametrization of the same curve.  This is how the
  parameter of a point of the curve is normalized to `0`, and how the two branches at that
  point are exchanged (`u = -1`);
* `AVD.IsProperLineParam.exists_ball_preimage_subset` — **small balls pull back to small
  parameter intervals**: for every `a` and every `δ > 0` there is `r > 0` with
  `γ ⁻¹' (ball (γ a) r) ⊆ (a - δ, a + δ)`.  Equivalently, a small enough ball around `γ a`
  meets the curve only in the piece `γ '' (a - δ, a + δ)` of it around `γ a`.

The second statement is the reason why an edge of a Voronoi diagram is, near one of its ends,
a *single branch* of the bisecting curve carrying it: see
`AbstractVoronoi/AVD/VertexDegree.lean`.
-/

noncomputable section

open Set Metric

namespace AVD

/-- **Affine reparametrization of a properly embedded line.**  If `γ` is a proper
parametrization of the curve `L` and `u ≠ 0`, then `t ↦ γ (c + u·t)` is again one: it is
continuous and injective, it has the same range, and the preimage of a compact set is the
image of a compact set under the affine inverse. -/
theorem IsProperLineParam.affine {γ : ℝ → Plane} {L : Set Plane} (hγ : IsProperLineParam γ L)
    (c : ℝ) {u : ℝ} (hu : u ≠ 0) : IsProperLineParam (fun t => γ (c + u * t)) L := by
  obtain ⟨hcont, hinj, hrange, hproper⟩ := hγ
  refine ⟨hcont.comp (by fun_prop), fun s t hst => ?_, ?_, fun K hK => ?_⟩
  · have := hinj hst
    have : u * s = u * t := by linarith
    exact mul_left_cancel₀ hu this
  · rw [← hrange]
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨t, rfl⟩
      exact ⟨c + u * t, rfl⟩
    · rintro x ⟨t, rfl⟩
      refine ⟨(t - c) / u, ?_⟩
      have h : c + u * ((t - c) / u) = t := by
        field_simp
        ring
      change γ (c + u * ((t - c) / u)) = γ t
      rw [h]
  · have himg : (fun t => γ (c + u * t)) ⁻¹' K = (fun s => (s - c) / u) '' (γ ⁻¹' K) := by
      ext t
      simp only [mem_preimage, mem_image]
      constructor
      · intro ht
        refine ⟨c + u * t, ht, ?_⟩
        field_simp
        ring
      · rintro ⟨s, hs, rfl⟩
        have hcs : c + u * ((s - c) / u) = s := by
          field_simp
          ring
        rwa [hcs]
    rw [himg]
    exact (hproper K hK).image (by fun_prop)

/-- **Small balls around a point of a properly embedded line pull back to small parameter
intervals.**

If `γ` is a proper parametrization of a curve and `δ > 0`, there is a radius `r > 0` such that
every parameter `t` with `γ t` inside the ball of radius `r` around `γ a` satisfies
`|t - a| < δ`.

This is properness: the set of parameters `t` with `|t - a| ⩾ δ` whose image lies in the
closed unit ball around `γ a` is compact, its image is a compact set missing `γ a` by
injectivity, and any ball around `γ a` avoiding that image works. -/
theorem IsProperLineParam.exists_ball_preimage_subset {γ : ℝ → Plane} {L : Set Plane}
    (hγ : IsProperLineParam γ L) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, γ ⁻¹' (ball (γ a) r) ⊆ Ioo (a - δ) (a + δ) := by
  obtain ⟨hcont, hinj, -, hproper⟩ := hγ
  have hK : IsCompact (γ ⁻¹' closedBall (γ a) 1) := hproper _ (isCompact_closedBall _ _)
  have hA : IsCompact (γ ⁻¹' closedBall (γ a) 1 \ Ioo (a - δ) (a + δ)) :=
    hK.diff isOpen_Ioo
  have hAim : IsCompact (γ '' (γ ⁻¹' closedBall (γ a) 1 \ Ioo (a - δ) (a + δ))) :=
    hA.image hcont
  have hnot : γ a ∉ γ '' (γ ⁻¹' closedBall (γ a) 1 \ Ioo (a - δ) (a + δ)) := by
    rintro ⟨t, ht, hteq⟩
    have hta : t = a := hinj hteq
    refine ht.2 ?_
    subst hta
    exact ⟨by linarith, by linarith⟩
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.1 hAim.isClosed.isOpen_compl _ hnot
  refine ⟨min r 1, lt_min hr one_pos, fun t ht => ?_⟩
  have htr : γ t ∈ ball (γ a) r := ball_subset_ball (min_le_left _ _) ht
  have ht1 : γ t ∈ closedBall (γ a) 1 :=
    ball_subset_closedBall (ball_subset_ball (min_le_right _ _) ht)
  by_contra hcon
  exact hball htr ⟨t, ⟨ht1, hcon⟩, rfl⟩

/-- **A subarc lying on one side of a parameter is, near the corresponding point, a single
branch.**

Let `γ₀` be a proper parametrization of a curve, let `I` be an order-connected non-empty set
of parameters lying strictly on one side of a parameter `a` in the closure of `I` (the side
being recorded by `u = 1` or `u = -1`, through `0 < u·(s - a)` for `s ∈ I`).  Reparametrize
by `γ t = γ₀ (a + u·t)`, so that `γ 0 = γ₀ a` and the set `I` corresponds to positive
parameters.  Then

* a whole initial branch `γ '' (0, b)`, `b > 0`, is contained in the arc `γ₀ '' I`;
* and conversely, for every `δ > 0` a small enough ball around `γ₀ a` meets the arc only
  inside the branch `γ '' (0, δ)`.

The second point is `AVD.IsProperLineParam.exists_ball_preimage_subset`; the first one uses
that `a` is in the closure of `I` and that `I` is order-connected.

This is the local picture of an **edge of a Voronoi diagram at one of its ends**, an edge
being an open subarc of a bisecting curve; see `AbstractVoronoi/AVD/VertexDegree.lean`. -/
theorem IsProperLineParam.exists_branch {γ₀ : ℝ → Plane} {L : Set Plane} {I : Set ℝ} {a u : ℝ}
    (hγ₀ : IsProperLineParam γ₀ L) (hord : I.OrdConnected) (hne : I.Nonempty)
    (hacl : a ∈ closure I) (hu : u = 1 ∨ u = -1) (hside : ∀ s ∈ I, 0 < u * (s - a)) :
    IsProperLineParam (fun t => γ₀ (a + u * t)) L ∧
      (∃ b > 0, (fun t => γ₀ (a + u * t)) '' Ioo 0 b ⊆ γ₀ '' I) ∧
      ∀ δ > 0, ∃ r > 0,
        γ₀ '' I ∩ ball (γ₀ a) r ⊆ (fun t => γ₀ (a + u * t)) '' Ioo 0 δ := by
  have hu0 : u ≠ 0 := by rcases hu with rfl | rfl <;> norm_num
  have hγ : IsProperLineParam (fun t => γ₀ (a + u * t)) L := hγ₀.affine a hu0
  have hγ0 : (fun t => γ₀ (a + u * t)) 0 = γ₀ a := by simp
  obtain ⟨c, hc⟩ := hne
  refine ⟨hγ, ⟨u * (c - a), hside c hc, ?_⟩, ?_⟩
  · -- the branch `γ '' (0, u·(c - a))` lies on the arc
    rintro x ⟨t, ⟨ht0, htb⟩, rfl⟩
    have hmem : a + u * t ∈ I := by
      -- a parameter of `I` closer to `a` than `t`
      obtain ⟨x, hxI, hxa⟩ := Metric.mem_closure_iff.1 hacl t ht0
      have hxu : 0 < u * (x - a) := hside x hxI
      have habs : |x - a| < t := by
        rw [Real.dist_eq, abs_sub_comm] at hxa
        exact hxa
      have hxt : u * (x - a) < t := by
        rcases hu with rfl | rfl
        · simp only [one_mul]
          calc x - a ≤ |x - a| := le_abs_self _
            _ < t := habs
        · have : -(x - a) ≤ |x - a| := neg_le_abs _
          simpa using lt_of_le_of_lt this habs
      refine hord.uIcc_subset hxI hc ?_
      rcases hu with rfl | rfl
      · simp only [one_mul] at hxt htb ⊢
        rw [Set.mem_uIcc]
        exact Or.inl ⟨by linarith, by linarith⟩
      · simp only [neg_mul, one_mul, neg_sub] at hxt htb ⊢
        rw [Set.mem_uIcc]
        exact Or.inr ⟨by linarith, by linarith⟩
    exact ⟨a + u * t, hmem, rfl⟩
  · -- near `γ₀ a`, the arc is inside the branch
    intro δ hδ
    obtain ⟨r, hr, hsub⟩ := hγ.exists_ball_preimage_subset 0 hδ
    refine ⟨r, hr, ?_⟩
    rintro x ⟨⟨s, hsI, rfl⟩, hball⟩
    have hu2 : u * u = 1 := by rcases hu with rfl | rfl <;> norm_num
    have hkey : a + u * (u * (s - a)) = s := by
      have : u * (u * (s - a)) = (u * u) * (s - a) := by ring
      rw [this, hu2, one_mul]
      ring
    have hmem : u * (s - a) ∈
        (fun t => γ₀ (a + u * t)) ⁻¹' ball ((fun t => γ₀ (a + u * t)) 0) r := by
      simp only [mem_preimage, hγ0]
      rw [hkey]
      exact hball
    have hlt := hsub hmem
    refine ⟨u * (s - a), ⟨hside s hsI, ?_⟩, ?_⟩
    · simpa using hlt.2
    · change γ₀ (a + u * (u * (s - a))) = γ₀ s
      rw [hkey]

end AVD
