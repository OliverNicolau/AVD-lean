import AbstractVoronoi.Jordan.ArcSurgery
import AbstractVoronoi.Jordan.CyclicParam
import AbstractVoronoi.Jordan.Backend

/-!
# The boundary of a complementary domain of a closed Jordan curve

This file proves one of the assertions of **Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

namely that the two domains `D₁, D₂` of `ℝ² \ C` produced by the Jordan curve theorem have
`C` as their **common boundary** — not merely a boundary contained in `C`, which is all the
Jordan curve theorem itself gives (`AVD.IsClosedJordanCurve.exists_separation_frontier`).

The classical route, which is the one followed here, is the *non-separation theorem for
arcs*: a simple arc does not separate the plane.  That theorem is available in the Lean 4
Jordan curve theorem development this project depends on, as
`JordanCurveTheorem.simple_arc_conn_complement`; it is restated here as
`AVD.exists_arc_avoiding_arc`.  Given `z ∈ C` and a small ball `B` around `z`, one removes
from `C` a short open piece around `z` contained in `B`; what is left is a simple arc `A`,
so a point `a ∈ D₁` and a point `b ∈ D₂` can be joined by an arc `γ` avoiding `A`.  Since
`γ` runs from `D₁` to `D₂` it must meet `C`, and it can only meet it in `C \ A ⊆ B`; the
piece of `γ` before its first meeting point lies in `D₁` and comes arbitrarily close to
that point, hence meets `B`.  So `B` meets `D₁`, and `z ∈ closure D₁`.
-/

noncomputable section

open Set Topology

namespace AVD

/-- **The non-separation theorem for arcs**: a simple arc does not separate the plane.

Two points off a simple arc `A` can be joined by an arc that avoids `A` altogether.  This
is `Backend.exists_arcBetween_compl_arc` (from the Lean 4 Jordan–Schönflies development),
transported to the notion of arc used here.  It is the classical ingredient
in the proof that the boundary of each complementary domain of a closed Jordan curve is
the whole curve, which is part of Theorem 4 of Klein–Langetepe–Nilforoushan (2009). -/
theorem exists_arc_avoiding_arc {A : Set Plane} (hA : Backend.IsArc A) {x y : Plane}
    (hx : x ∉ A) (hy : y ∉ A) (hxy : x ≠ y) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = y ∧ Disjoint A (γ '' Icc 0 1) := by
  obtain ⟨B, hB, hBsub⟩ := Backend.exists_arcBetween_compl_arc hA hxy hx hy
  obtain ⟨γ, hγ, h0, h1, himg⟩ := exists_isArc_of_isArcBetween hB
  refine ⟨γ, hγ, h0, h1, ?_⟩
  rw [himg]
  exact Set.disjoint_right.2 fun w hw => hBsub hw

/-- The first point at which a path meets a closed set, in the form needed below: if `γ` is
continuous on `[0,1]`, `K` is closed, `γ 0 ∉ K` and `γ t₁ ∈ K` for some `t₁ ∈ [0,1]`, then
there is a first parameter `t` at which `γ` meets `K`. -/
theorem exists_first_meet {γ : ℝ → Plane} (hcont : ContinuousOn γ (Icc 0 1)) {K : Set Plane}
    (hK : IsClosed K) (h0 : γ 0 ∉ K) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (h1 : γ t₁ ∈ K) :
    ∃ t ∈ Ioc (0 : ℝ) 1, γ t ∈ K ∧ ∀ s ∈ Ico (0 : ℝ) t, γ s ∉ K := by
  set T : Set ℝ := Icc 0 1 ∩ γ ⁻¹' K with hT
  have hTclosed : IsClosed T := hcont.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hTne : T.Nonempty := ⟨t₁, ht₁, h1⟩
  have hTbdd : BddBelow T := ⟨0, fun x hx => hx.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTclosed.csInf_mem hTne hTbdd
  have hlb : ∀ s ∈ T, t ≤ s := fun s hs => csInf_le hTbdd hs
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le htT.1.1 with h | h
    · exact absurd (by rw [← h] at htT; exact htT.2) h0
    · exact h
  refine ⟨t, ⟨htpos, htT.1.2⟩, htT.2, ?_⟩
  intro s hs hsK
  exact absurd (hlb s ⟨⟨hs.1, le_trans hs.2.le htT.1.2⟩, hsK⟩) (not_le.2 hs.2)

/-- **Every point of a closed Jordan curve lies in the closure of each complementary
domain.**

This is the assertion "`ℝ² \ C` consists of two domains `D₁, D₂` with **common boundary**
`C`" of Theorem 4 of Klein–Langetepe–Nilforoushan (2009); only the inclusion `C ⊆ closure D`
is proved here, the reverse inclusion `frontier D ⊆ C` being part of
`AVD.IsClosedJordanCurve.exists_separation_frontier`.

The proof is the classical one described in the header of this file. -/
theorem IsClosedJordanCurve.subset_closure_of_separation {C : Set Plane}
    (hC : IsClosedJordanCurve C) {D E : Set Plane} (hDo : IsOpen D) (hEo : IsOpen E)
    (hdisj : Disjoint D E) (hunion : D ∪ E = Cᶜ) (hD : D.Nonempty) (hE : E.Nonempty) :
    C ⊆ closure D := by
  intro z hz
  rw [mem_closure_iff]
  intro V hVopen hzV
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  have hVD : ∀ x ∈ V, x ∉ D := by
    intro x hxV hxD
    have : x ∈ V ∩ D := ⟨hxV, hxD⟩
    rw [hcon] at this
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVopen z hzV
  -- a cyclic parametrization of the curve
  obtain ⟨Γ, hΓ⟩ := hC.exists_cyclicParam
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, Γ t₀ = z := by rw [← hΓ.range_eq] at hz; exact hz
  -- a short piece of the curve around `z`, inside the ball
  obtain ⟨η, hη, hηsub⟩ : ∃ η > (0 : ℝ), ∀ t, |t - t₀| < η → Γ t ∈ Metric.ball z ε := by
    have hcontat : ContinuousAt Γ t₀ := hΓ.cont.continuousAt
    have := Metric.tendsto_nhds.1 hcontat ε hε
    rw [Metric.eventually_nhds_iff] at this
    obtain ⟨η, hη, hsub⟩ := this
    refine ⟨η, hη, fun t htt => ?_⟩
    have : dist t t₀ < η := by rwa [Real.dist_eq]
    have h2 := hsub this
    rw [ht₀] at h2
    exact Metric.mem_ball.2 h2
  set δ : ℝ := min (η / 2) (1 / 4) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδη : δ < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hshort : Γ '' Icc (t₀ - δ) (t₀ + δ) ⊆ Metric.ball z ε := by
    rintro x ⟨t, ht, rfl⟩
    refine hηsub t ?_
    rw [abs_lt]
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  -- the complementary piece is a simple arc
  set A : Set Plane := Γ '' Icc (t₀ + δ) (t₀ - δ + 1) with hAdef
  have hlt : t₀ + δ < t₀ - δ + 1 := by linarith
  have hlen : (t₀ - δ + 1) - (t₀ + δ) < 1 := by linarith
  obtain ⟨κ, hκcont, hκinj, -, -, hκimg⟩ := hΓ.exists_param_Icc hlt hlen
  have hAarc : Backend.IsArc A := ⟨κ, hκcont.continuousOn, hκinj, by rw [hAdef, ← hκimg]⟩
  have hAC : A ⊆ C := by
    rintro x ⟨t, -, rfl⟩
    rw [← hΓ.range_eq]; exact mem_range_self t
  have hCA : C \ A ⊆ Metric.ball z ε := by
    intro x hx
    have := hΓ.image_union (a := t₀ - δ) (b := t₀ + δ) (by linarith) (by linarith)
    rw [show t₀ - δ + 1 = t₀ - δ + 1 from rfl] at this
    have hxC : x ∈ Γ '' Icc (t₀ - δ) (t₀ + δ) ∪ A := by rw [hAdef, this]; exact hx.1
    rcases hxC with h | h
    · exact hshort h
    · exact absurd h hx.2
  -- an arc from `D` to `E` avoiding the complementary piece
  obtain ⟨a, ha⟩ := hD
  obtain ⟨b, hb⟩ := hE
  have haC : a ∉ C := by
    have : a ∈ Cᶜ := by rw [← hunion]; exact Or.inl ha
    exact this
  have hbC : b ∉ C := by
    have : b ∈ Cᶜ := by rw [← hunion]; exact Or.inr hb
    exact this
  have hab : a ≠ b := fun h => (Set.disjoint_left.1 hdisj) ha (h ▸ hb)
  obtain ⟨γ, hγ, hγ0, hγ1, hγdisj⟩ :=
    exists_arc_avoiding_arc hAarc (fun h => haC (hAC h)) (fun h => hbC (hAC h)) hab
  -- the arc must meet the curve
  have hCclosed : IsClosed C := hC.isCompact.isClosed
  have hmeet : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ C := by
    by_contra hno
    push Not at hno
    have hsub : γ '' Icc 0 1 ⊆ D ∪ E := by
      rintro x ⟨t, ht, rfl⟩
      rw [hunion]
      exact hno t ht
    have hpre : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hγ.cont
    rcases hpre.subset_or_subset hDo hEo hdisj hsub with h | h
    · refine (Set.disjoint_left.1 hdisj) (h ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩) ?_
      rw [hγ1]; exact hb
    · refine (Set.disjoint_left.1 hdisj) ?_ (h ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩)
      rw [hγ0]; exact ha
  obtain ⟨t₁, ht₁, ht₁C⟩ := hmeet
  have hγ0C : γ 0 ∉ C := by rw [hγ0]; exact haC
  obtain ⟨t, htmem, htC, hfirst⟩ := exists_first_meet hγ.cont hCclosed hγ0C ht₁ ht₁C
  -- the first meeting point lies in the short piece, hence in the ball
  have htA : γ t ∉ A := fun h =>
    (Set.disjoint_left.1 hγdisj) h ⟨t, ⟨htmem.1.le, htmem.2⟩, rfl⟩
  have htball : γ t ∈ Metric.ball z ε := hCA ⟨htC, htA⟩
  -- the piece of the arc before `t` lies in `D`
  have hbefore : γ '' Ico 0 t ⊆ D := by
    have hsub : γ '' Ico 0 t ⊆ D ∪ E := by
      rintro x ⟨s, hs, rfl⟩
      rw [hunion]
      exact hfirst s hs
    have hpre : IsPreconnected (γ '' Ico 0 t) :=
      isPreconnected_Ico.image γ (hγ.cont.mono (fun s hs =>
        ⟨hs.1, le_trans hs.2.le htmem.2⟩))
    rcases hpre.subset_or_subset hDo hEo hdisj hsub with h | h
    · exact h
    · exact absurd (h ⟨0, ⟨le_refl 0, htmem.1⟩, rfl⟩)
        (fun hx => (Set.disjoint_left.1 hdisj) (by rw [← hγ0] at ha; exact ha) hx)
  -- and it comes arbitrarily close to `γ t`, hence meets the ball
  obtain ⟨ε', hε', hε'sub⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball (γ t) htball
  obtain ⟨θ, hθ, hθsub⟩ := Metric.continuousOn_iff.1 hγ.cont t ⟨htmem.1.le, htmem.2⟩ ε' hε'
  set s : ℝ := max 0 (t - θ / 2) with hsdef
  have hs0 : 0 ≤ s := le_max_left _ _
  have hst : s < t := by
    rcases le_or_gt (t - θ / 2) 0 with h | h
    · rw [hsdef, max_eq_left h]; exact htmem.1
    · rw [hsdef, max_eq_right h.le]; linarith
  have hsdist : dist s t < θ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    rcases le_or_gt (t - θ / 2) 0 with h | h
    · rw [hsdef, max_eq_left h]; linarith [htmem.2]
    · rw [hsdef, max_eq_right h.le]; linarith
  have hsball : γ s ∈ Metric.ball z ε :=
    hε'sub (Metric.mem_ball.2 (hθsub s ⟨hs0, le_trans hst.le htmem.2⟩ hsdist))
  exact hVD (γ s) (hball hsball) (hbefore ⟨s, ⟨hs0, hst⟩, rfl⟩)

/-- **The Jordan curve theorem in the form of Theorem 4** of
Klein–Langetepe–Nilforoushan (2009), for a closed Jordan curve, as far as the *global*
assertions of that theorem go:

> `ℝ² \ C` consists of two domains `D₁, D₂` with common boundary `C`,

and, `C` being compact, exactly one of the two domains is bounded.

This strengthens `AVD.IsClosedJordanCurve.exists_separation_frontier`, which only gives the
inclusions `frontier Dᵢ ⊆ C`; the reverse inclusions come from the non-separation theorem
for arcs, through `AVD.IsClosedJordanCurve.subset_closure_of_separation`. -/
theorem IsClosedJordanCurve.exists_separation_frontier_eq {C : Set Plane}
    (h : IsClosedJordanCurve C) :
    ∃ D₁ D₂ : Set Plane, IsOpen D₁ ∧ IsOpen D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧
      Disjoint D₁ D₂ ∧ D₁ ∪ D₂ = Cᶜ ∧ frontier D₁ = C ∧ frontier D₂ = C ∧
      ((Bornology.IsBounded D₁ ∧ ¬ Bornology.IsBounded D₂) ∨
        (Bornology.IsBounded D₂ ∧ ¬ Bornology.IsBounded D₁)) := by
  obtain ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, hf1, hf2, hbdd⟩ :=
    h.exists_separation_frontier
  have key : ∀ D E : Set Plane, IsOpen D → IsOpen E → Disjoint D E → D ∪ E = Cᶜ →
      D.Nonempty → E.Nonempty → frontier D ⊆ C → frontier D = C := by
    intro D E hDo hEo hdis hun hDne hEne hsub
    refine Subset.antisymm hsub (fun z hz => ?_)
    have hcl : z ∈ closure D :=
      h.subset_closure_of_separation hDo hEo hdis hun hDne hEne hz
    have hzD : z ∉ D := by
      intro hzD
      have : z ∈ Cᶜ := by rw [← hun]; exact Or.inl hzD
      exact this hz
    rw [hDo.frontier_eq]
    exact ⟨hcl, hzD⟩
  refine ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, ?_, ?_, hbdd⟩
  · exact key D₁ D₂ h1o h2o hdisj hunion h1c.nonempty h2c.nonempty hf1
  · exact key D₂ D₁ h2o h1o hdisj.symm (by rw [union_comm]; exact hunion)
      h2c.nonempty h1c.nonempty hf2

end AVD
