import AbstractVoronoi.Jordan.ThetaCurve
import AbstractVoronoi.Jordan.CrosscutNear

/-!
# The local part of Theorem 4 from local connectedness

This file proves the **local part of Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

from the sole assumption that the two complementary domains of the curve are locally
connected at every point of it (`AVD.LocallyConnectedAt`).

The construction is isolated in `AVD.exists_local_nbhd_of_data`, which takes as input a small
arc `g₁` of the curve through `z` and two crosscuts `k₁ ⊆ D₁`, `k₂ ⊆ D₂` with the endpoints
of `g₁` as endpoints, together with the small domains `Ω₁, Ω₂` they cut off; the
neighbourhood of the statement is then `U = Ω₁ ∪ Ω₂ ∪ g₁ '' Ioo 0 1`, whose frontier is the
closed Jordan curve `k₁ ∪ k₂`.  The two ingredients are the small crosscuts with prescribed
endpoints `AVD.exists_crosscut_near` and the local absorption lemma
`AVD.exists_ball_inter_subset`.

`AVD.IsClosedJordanCurve.exists_local_nbhd` then assembles the data for a closed Jordan
curve.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- **The local part of Theorem 4** of Klein–Langetepe–Nilforoushan (2009), from the data of
a small arc of the curve around `z` and of two crosscuts with the endpoints of that arc:

> For each point `z ∈ C` there exists a neighbourhood `U` whose boundary is homeomorphic to
> a circle, such that `U \ C` consists of exactly two connected components.  Point `z` is
> accessible from each domain `U ∩ Dᵢ`.

Here `D₁, D₂` are the two complementary domains of the curve `C`, assumed locally connected
at every point of `C`; `g₁` is an arc of `C`, with endpoints `a, b`, containing `z` in its
relative interior, whose complement `A₂` in `C` is closed; and `k₁, k₂` are arcs from `a` to
`b` whose relative interiors run inside `D₁ ∩ ball z ε₁` and `D₂ ∩ ball z ε₁`.  Finally `Ωᵢ`
is the domain cut off in `Dᵢ` by `kᵢ` along `g₁`, i.e. the domain with
`frontier Ωᵢ = kᵢ ∪ g₁`, assumed to be contained in the ball of radius `ε₁` around `z`.

The neighbourhood produced is `U = Ω₁ ∪ Ω₂ ∪ g₁ '' Ioo 0 1`; that it is *open* is the
content of the local absorption lemma `AVD.exists_ball_inter_subset`, and its frontier is
the closed Jordan curve `k₁ ∪ k₂`. -/
theorem exists_local_nbhd_of_data {C D₁ D₂ A₂ Ω₁ Ω₂ : Set Plane} {g₁ k₁ k₂ : ℝ → Plane}
    {a b z : Plane} {ε₁ : ℝ}
    (h1o : IsOpen D₁) (h2o : IsOpen D₂) (hdisj : Disjoint D₁ D₂) (hunion : D₁ ∪ D₂ = Cᶜ)
    (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    (hlc1 : ∀ y ∈ C, LocallyConnectedAt D₁ y) (hlc2 : ∀ y ∈ C, LocallyConnectedAt D₂ y)
    (hz : z ∈ C)
    (harc₁ : IsArc g₁) (hk₁ : IsArc k₁) (hk₂ : IsArc k₂)
    (h₁₀ : g₁ 0 = a) (h₁₁ : g₁ 1 = b)
    (hk₁₀ : k₁ 0 = a) (hk₁₁ : k₁ 1 = b) (hk₂₀ : k₂ 0 = a) (hk₂₁ : k₂ 1 = b)
    (hk₁sub : k₁ '' Ioo 0 1 ⊆ D₁ ∩ ball z ε₁) (hk₂sub : k₂ '' Ioo 0 1 ⊆ D₂ ∩ ball z ε₁)
    (hA₂closed : IsClosed A₂) (hCeq : g₁ '' Icc 0 1 ∪ A₂ = C)
    (hI₁A₂ : Disjoint (g₁ '' Ioo 0 1) A₂) (habA₂ : a ∈ A₂ ∧ b ∈ A₂)
    (hA₁ball : g₁ '' Icc 0 1 ⊆ ball z ε₁) (hzI₁ : z ∈ g₁ '' Ioo 0 1)
    (hΩ₁o : IsOpen Ω₁) (hΩ₁c : IsConnected Ω₁) (hΩ₁D : Ω₁ ⊆ D₁)
    (hfΩ₁ : frontier Ω₁ = k₁ '' Icc 0 1 ∪ g₁ '' Icc 0 1) (hΩ₁small : Ω₁ ⊆ closedBall z ε₁)
    (hΩ₂o : IsOpen Ω₂) (hΩ₂c : IsConnected Ω₂) (hΩ₂D : Ω₂ ⊆ D₂)
    (hfΩ₂ : frontier Ω₂ = k₂ '' Icc 0 1 ∪ g₁ '' Icc 0 1) (hΩ₂small : Ω₂ ⊆ closedBall z ε₁) :
    ∃ U : Set Plane, IsOpen U ∧ z ∈ U ∧ U ⊆ closedBall z ε₁ ∧
      IsClosedJordanCurve (frontier U) ∧
      IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
      (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
      (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z) := by
  classical
  -- the two domains avoid the curve
  have hD₁C : Disjoint D₁ C := by
    rw [← hf1, h1o.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  have hD₂C : Disjoint D₂ C := by
    rw [← hf2, h2o.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  have hcover : ∀ w : Plane, w ∈ C ∨ w ∈ D₁ ∨ w ∈ D₂ := by
    intro w
    by_cases hw : w ∈ C
    · exact Or.inl hw
    · have : w ∈ D₁ ∪ D₂ := by rw [hunion]; exact hw
      exact Or.inr this
  set A₁ : Set Plane := g₁ '' Icc 0 1 with hA₁
  set I₁ : Set Plane := g₁ '' Ioo 0 1 with hI₁
  set K₁ : Set Plane := k₁ '' Icc 0 1 with hK₁
  set K₂ : Set Plane := k₂ '' Icc 0 1 with hK₂
  have hA₁C : A₁ ⊆ C := by rw [← hCeq]; exact subset_union_left
  have hI₁A₁ : I₁ ⊆ A₁ := Set.image_mono Ioo_subset_Icc_self
  have hzA₁ : z ∈ A₁ := hI₁A₁ hzI₁
  have hA₁split : A₁ = I₁ ∪ {a, b} := by
    rw [hA₁, hI₁, image_Icc_eq_union_endpoints, h₁₀, h₁₁]
  have hK₁split : K₁ = k₁ '' Ioo 0 1 ∪ {a, b} := by
    rw [hK₁, image_Icc_eq_union_endpoints, hk₁₀, hk₁₁]
  have hK₂split : K₂ = k₂ '' Ioo 0 1 ∪ {a, b} := by
    rw [hK₂, image_Icc_eq_union_endpoints, hk₂₀, hk₂₁]
  have hK₁closed : IsClosed K₁ := (isCompact_Icc.image_of_continuousOn hk₁.cont).isClosed
  have hK₂closed : IsClosed K₂ := (isCompact_Icc.image_of_continuousOn hk₂.cont).isClosed
  have haA₁ : a ∈ A₁ := by rw [hA₁, ← h₁₀]; exact ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have hbA₁ : b ∈ A₁ := by rw [hA₁, ← h₁₁]; exact ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
  have haC : a ∈ C := hA₁C haA₁
  have hbC : b ∈ C := hA₁C hbA₁
  have hΩ₁K : Disjoint Ω₁ K₁ := by
    refine Set.disjoint_left.2 fun w hw hwK => ?_
    have : w ∈ frontier Ω₁ := by rw [hfΩ₁]; exact Or.inl hwK
    exact (hΩ₁o.frontier_eq ▸ this).2 hw
  have hΩ₂K : Disjoint Ω₂ K₂ := by
    refine Set.disjoint_left.2 fun w hw hwK => ?_
    have : w ∈ frontier Ω₂ := by rw [hfΩ₂]; exact Or.inl hwK
    exact (hΩ₂o.frontier_eq ▸ this).2 hw
  -- the neighbourhood
  set U : Set Plane := Ω₁ ∪ Ω₂ ∪ I₁ with hUdef
  -- the local picture at a point of the small arc
  have hlocal : ∀ y ∈ I₁, ∃ ρ > 0, ball y ρ ⊆ U ∧ ball y ρ ∩ D₁ ⊆ Ω₁ ∧
      ball y ρ ∩ D₂ ⊆ Ω₂ := by
    intro y hy
    have hyC : y ∈ C := hA₁C (hI₁A₁ hy)
    have hyA₂ : y ∉ A₂ := fun h => (Set.disjoint_left.1 hI₁A₂) hy h
    have hyab : y ≠ a ∧ y ≠ b := by
      constructor <;> intro hcon <;> exact hyA₂ (hcon ▸ (by
        first
          | exact habA₂.1
          | exact habA₂.2))
    have hyK₁ : y ∉ K₁ := by
      rw [hK₁split]
      rintro (hw | hw)
      · exact (Set.disjoint_left.1 hD₁C) (hk₁sub hw).1 hyC
      · rcases hw with h | h
        · exact hyab.1 h
        · exact hyab.2 h
    have hyK₂ : y ∉ K₂ := by
      rw [hK₂split]
      rintro (hw | hw)
      · exact (Set.disjoint_left.1 hD₂C) (hk₂sub hw).1 hyC
      · rcases hw with h | h
        · exact hyab.1 h
        · exact hyab.2 h
    have hFclosed : IsClosed (K₁ ∪ K₂ ∪ A₂) :=
      (hK₁closed.union hK₂closed).union hA₂closed
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hFclosed.isOpen_compl y (by
      rintro ((h | h) | h)
      · exact hyK₁ h
      · exact hyK₂ h
      · exact hyA₂ h)
    have hballK₁ : Disjoint (ball y ρ) K₁ :=
      Set.disjoint_left.2 fun w hw hw' => (hρsub hw) (Or.inl (Or.inl hw'))
    have hballK₂ : Disjoint (ball y ρ) K₂ :=
      Set.disjoint_left.2 fun w hw hw' => (hρsub hw) (Or.inl (Or.inr hw'))
    have hballA₂ : Disjoint (ball y ρ) A₂ :=
      Set.disjoint_left.2 fun w hw hw' => (hρsub hw) (Or.inr hw')
    -- the local absorption lemma: near `y`, the domains `Dᵢ` are swallowed by `Ωᵢ`
    have hycl₁ : y ∈ closure Ω₁ :=
      frontier_subset_closure (by rw [hfΩ₁]; exact Or.inr (hI₁A₁ hy))
    have hycl₂ : y ∈ closure Ω₂ :=
      frontier_subset_closure (by rw [hfΩ₂]; exact Or.inr (hI₁A₁ hy))
    obtain ⟨ρ₁, hρ₁, hρ₁le, hsub₁⟩ :=
      exists_ball_inter_subset h1o hD₁C hK₁closed hΩ₁o hΩ₁D hfΩ₁ hA₁C (hlc1 y hyC) hycl₁
        hρ hballK₁
    obtain ⟨ρ₂, hρ₂, hρ₂le, hsub₂⟩ :=
      exists_ball_inter_subset h2o hD₂C hK₂closed hΩ₂o hΩ₂D hfΩ₂ hA₁C (hlc2 y hyC) hycl₂
        hρ hballK₂
    have hD₁sub : ball y (min ρ₁ ρ₂) ∩ D₁ ⊆ Ω₁ := fun w hw =>
      hsub₁ ⟨ball_subset_ball (min_le_left _ _) hw.1, hw.2⟩
    have hD₂sub : ball y (min ρ₁ ρ₂) ∩ D₂ ⊆ Ω₂ := fun w hw =>
      hsub₂ ⟨ball_subset_ball (min_le_right _ _) hw.1, hw.2⟩
    have hballA₂' : Disjoint (ball y (min ρ₁ ρ₂)) A₂ :=
      Disjoint.mono_left (ball_subset_ball (le_trans (min_le_left _ _) hρ₁le)) hballA₂
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_, hD₁sub, hD₂sub⟩
    intro w hw
    rcases hcover w with hwC | hwD₁ | hwD₂
    · refine Or.inr ?_
      have : w ∈ A₁ ∪ A₂ := by rw [hCeq]; exact hwC
      rcases this with h | h
      · rcases (hA₁split ▸ h : w ∈ I₁ ∪ {a, b}) with h' | h'
        · exact h'
        · rcases h' with rfl | rfl
          · exact absurd habA₂.1 (Set.disjoint_left.1 hballA₂' hw)
          · exact absurd habA₂.2 (Set.disjoint_left.1 hballA₂' hw)
      · exact absurd h (Set.disjoint_left.1 hballA₂' hw)
    · exact Or.inl (Or.inl (hD₁sub ⟨hw, hwD₁⟩))
    · exact Or.inl (Or.inr (hD₂sub ⟨hw, hwD₂⟩))
  -- `U` is open
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ((hy | hy) | hy)
    · exact ⟨Ω₁, fun w hw => Or.inl (Or.inl hw), hΩ₁o, hy⟩
    · exact ⟨Ω₂, fun w hw => Or.inl (Or.inr hw), hΩ₂o, hy⟩
    · obtain ⟨ρ, hρ, hρU, -, -⟩ := hlocal y hy
      exact ⟨ball y ρ, hρU, isOpen_ball, mem_ball_self hρ⟩
  have hzU : z ∈ U := Or.inr hzI₁
  -- the trace of `U` on the two domains
  have hUD₁ : U ∩ D₁ = Ω₁ := by
    apply Subset.antisymm
    · rintro w ⟨(hw | hw) | hw, hwD⟩
      · exact hw
      · exact absurd (hΩ₂D hw) (Set.disjoint_left.1 hdisj hwD)
      · exact absurd (hA₁C (hI₁A₁ hw)) (Set.disjoint_left.1 hD₁C hwD)
    · exact fun w hw => ⟨Or.inl (Or.inl hw), hΩ₁D hw⟩
  have hUD₂ : U ∩ D₂ = Ω₂ := by
    apply Subset.antisymm
    · rintro w ⟨(hw | hw) | hw, hwD⟩
      · exact absurd (hΩ₁D hw) (Set.disjoint_right.1 hdisj hwD)
      · exact hw
      · exact absurd (hA₁C (hI₁A₁ hw)) (Set.disjoint_left.1 hD₂C hwD)
    · exact fun w hw => ⟨Or.inl (Or.inr hw), hΩ₂D hw⟩
  -- the frontier of `U` is the closed Jordan curve `K₁ ∪ K₂`
  have hKU₁ : Disjoint K₁ U := by
    refine Set.disjoint_left.2 ?_
    rintro w hw ((h | h) | h)
    · exact (Set.disjoint_left.1 hΩ₁K h) hw
    · rw [hK₁split] at hw
      rcases hw with hw | hw
      · exact (Set.disjoint_left.1 hdisj) (hk₁sub hw).1 (hΩ₂D h)
      · rcases hw with rfl | rfl
        · exact (Set.disjoint_left.1 hD₂C) (hΩ₂D h) haC
        · exact (Set.disjoint_left.1 hD₂C) (hΩ₂D h) hbC
    · rw [hK₁split] at hw
      rcases hw with hw | hw
      · exact (Set.disjoint_left.1 hD₁C) (hk₁sub hw).1 (hA₁C (hI₁A₁ h))
      · have hd := harc₁.image_Ioo_subset_diff h
        rw [h₁₀, h₁₁] at hd
        exact hd.2 hw
  have hKU₂ : Disjoint K₂ U := by
    refine Set.disjoint_left.2 ?_
    rintro w hw ((h | h) | h)
    · rw [hK₂split] at hw
      rcases hw with hw | hw
      · exact (Set.disjoint_left.1 hdisj) (hΩ₁D h) (hk₂sub hw).1
      · rcases hw with rfl | rfl
        · exact (Set.disjoint_left.1 hD₁C) (hΩ₁D h) haC
        · exact (Set.disjoint_left.1 hD₁C) (hΩ₁D h) hbC
    · exact (Set.disjoint_left.1 hΩ₂K h) hw
    · rw [hK₂split] at hw
      rcases hw with hw | hw
      · exact (Set.disjoint_left.1 hD₂C) (hk₂sub hw).1 (hA₁C (hI₁A₁ h))
      · have hd := harc₁.image_Ioo_subset_diff h
        rw [h₁₀, h₁₁] at hd
        exact hd.2 hw
  have hfrontU : frontier U = K₁ ∪ K₂ := by
    have hclos : ∀ S : Set Plane, IsOpen S → closure S ⊆ S ∪ frontier S := by
      intro S hS w hw
      by_cases h : w ∈ S
      · exact Or.inl h
      · exact Or.inr ⟨hw, by rwa [hS.interior_eq]⟩
    have hA₁U : A₁ ⊆ U ∪ K₁ := by
      rw [hA₁split]
      rintro w (hw | hw)
      · exact Or.inl (Or.inr hw)
      · refine Or.inr ?_
        rw [hK₁split]
        exact Or.inr hw
    apply Subset.antisymm
    · intro w hw
      have hwU : w ∉ U := by
        have := hw.2
        rwa [hUopen.interior_eq] at this
      have hwc : w ∈ closure U := hw.1
      rw [hUdef, closure_union, closure_union] at hwc
      rcases hwc with (h | h) | h
      · rcases hclos _ hΩ₁o h with h' | h'
        · exact absurd (Or.inl (Or.inl h') : w ∈ U) hwU
        · rw [hfΩ₁] at h'
          rcases h' with h'' | h''
          · exact Or.inl h''
          · rcases hA₁U h'' with h''' | h'''
            · exact absurd h''' hwU
            · exact Or.inl h'''
      · rcases hclos _ hΩ₂o h with h' | h'
        · exact absurd (Or.inl (Or.inr h') : w ∈ U) hwU
        · rw [hfΩ₂] at h'
          rcases h' with h'' | h''
          · exact Or.inr h''
          · rcases hA₁U h'' with h''' | h'''
            · exact absurd h''' hwU
            · exact Or.inl h'''
      · have : closure I₁ ⊆ A₁ := by
          refine closure_minimal hI₁A₁ ?_
          exact (isCompact_Icc.image_of_continuousOn harc₁.cont).isClosed
        rcases hA₁U (this h) with h' | h'
        · exact absurd h' hwU
        · exact Or.inl h'
    · rintro w (hw | hw)
      · refine ⟨?_, ?_⟩
        · have : w ∈ closure Ω₁ :=
            frontier_subset_closure (by rw [hfΩ₁]; exact Or.inl hw)
          exact closure_mono (fun v hv => (Or.inl (Or.inl hv) : v ∈ U)) this
        · rw [hUopen.interior_eq]
          exact Set.disjoint_left.1 hKU₁ hw
      · refine ⟨?_, ?_⟩
        · have : w ∈ closure Ω₂ :=
            frontier_subset_closure (by rw [hfΩ₂]; exact Or.inl hw)
          exact closure_mono (fun v hv => (Or.inl (Or.inr hv) : v ∈ U)) this
        · rw [hUopen.interior_eq]
          exact Set.disjoint_left.1 hKU₂ hw
  have hJordan : IsClosedJordanCurve (frontier U) := by
    rw [hfrontU]
    refine isClosedJordanCurve_of_arcs hk₁ hk₂ (by rw [hk₁₀, hk₂₀]) (by rw [hk₁₁, hk₂₁]) ?_
    exact Set.disjoint_left.2 fun w hw hw' =>
      (Set.disjoint_left.1 hdisj) (hk₁sub hw).1 (hk₂sub hw').1
  -- accessibility of `z` inside each of the two domains
  have haccess : ∀ (Ω D : Set Plane), IsOpen Ω → IsConnected Ω → Ω ⊆ D →
      LocallyConnectedAt D z → (∃ ρ > 0, ball z ρ ∩ D ⊆ Ω) → z ∉ Ω → z ∈ closure Ω →
      ∀ x ∈ Ω, AccessibleWithin Ω x z := by
    intro Ω D hΩo hΩc hΩD hlcD hρ hzΩ hzcl
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := hρ
    have hlcΩ : LocallyConnectedAt Ω z := by
      intro e he
      obtain ⟨d, hd, hjoin⟩ := hlcD (min e ρ₀) (lt_min he hρ₀)
      refine ⟨d, hd, ?_⟩
      intro x hx y hy
      refine (hjoin x ⟨hΩD hx.1, hx.2⟩ y ⟨hΩD hy.1, hy.2⟩).mono ?_
      rintro w ⟨hwD, hwb⟩
      exact ⟨hρ₀sub ⟨ball_subset_ball (min_le_right e ρ₀) hwb, hwD⟩,
        ball_subset_ball (min_le_left e ρ₀) hwb⟩
    obtain ⟨V, -, -, -, ⟨v, hv⟩, hVΩ, -, -, -, -, hVacc⟩ :=
      exists_locally_connected_nbhd hΩo hzΩ hzcl hlcΩ one_pos
    have hzacc : AccessibleFrom Ω z :=
      AccessibleFrom.mono hVΩ (AccessibleFrom.of_within (hVacc v hv))
    have hconn : ∀ x ∈ Ω, ∀ y ∈ Ω, JoinedIn Ω x y := by
      have hpc := (hΩo.isConnected_iff_isPathConnected).1 hΩc
      exact fun x hx y hy => hpc.joinedIn x hx y hy
    intro x hx
    have hxz : x ≠ z := fun h => hzΩ (h ▸ hx)
    obtain ⟨γ, hγ, h0, h1, hsub⟩ :=
      exists_arc_of_accessible hΩo hconn hxz (accessibleFrom_of_mem hΩo hx) hzacc
    refine ⟨γ, hγ, h0, h1, ?_⟩
    rintro w ⟨c, hc, rfl⟩
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h, h0]; exact hx
    · exact hsub ⟨c, ⟨h, hc.2⟩, rfl⟩
  obtain ⟨ρz, hρz, -, hρzD₁, hρzD₂⟩ := hlocal z hzI₁
  have hzΩ₁ : z ∉ Ω₁ := fun h => (Set.disjoint_left.1 hD₁C) (hΩ₁D h) hz
  have hzΩ₂ : z ∉ Ω₂ := fun h => (Set.disjoint_left.1 hD₂C) (hΩ₂D h) hz
  have hzcl₁ : z ∈ closure Ω₁ :=
    frontier_subset_closure (by rw [hfΩ₁]; exact Or.inr hzA₁)
  have hzcl₂ : z ∈ closure Ω₂ :=
    frontier_subset_closure (by rw [hfΩ₂]; exact Or.inr hzA₁)
  refine ⟨U, hUopen, hzU, ?_, hJordan, by rw [hUD₁]; exact hΩ₁c,
    by rw [hUD₂]; exact hΩ₂c, ?_, ?_⟩
  · rintro w ((hw | hw) | hw)
    · exact hΩ₁small hw
    · exact hΩ₂small hw
    · exact ball_subset_closedBall (hA₁ball (hI₁A₁ hw))
  · rw [hUD₁]
    exact haccess Ω₁ D₁ hΩ₁o hΩ₁c hΩ₁D (hlc1 z hz) ⟨ρz, hρz, hρzD₁⟩ hzΩ₁ hzcl₁
  · rw [hUD₂]
    exact haccess Ω₂ D₂ hΩ₂o hΩ₂c hΩ₂D (hlc2 z hz) ⟨ρz, hρz, hρzD₂⟩ hzΩ₂ hzcl₂

/-- **The local part of Theorem 4** of Klein–Langetepe–Nilforoushan (2009) for a *closed*
Jordan curve, derived from the local connectedness of the two complementary domains at the
points of the curve:

> For each point `z ∈ C` there exists a neighbourhood `U` whose boundary is homeomorphic to
> a circle, such that `U \ C` consists of exactly two connected components.  Point `z` is
> accessible from each domain `U ∩ Dᵢ`.

The data required by `AVD.exists_local_nbhd_of_data` are assembled here: a cyclic
parametrization of `C` cuts out a small arc `g₁` around `z`, whose endpoints `a, b` are
joined inside each `Dᵢ` by a small crosscut `kᵢ` (`AVD.exists_crosscut_near`); the small
domains `Ωᵢ` come from the crosscut theorem `AVD.exists_crosscut_domains` and are small by
`AVD.subset_closedBall_of_frontier_subset`. -/
theorem IsClosedJordanCurve.exists_local_nbhd {C D₁ D₂ : Set Plane}
    (hC : IsClosedJordanCurve C) (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (hdisj : Disjoint D₁ D₂) (hunion : D₁ ∪ D₂ = Cᶜ)
    (hf1 : frontier D₁ = C) (hf2 : frontier D₂ = C)
    (hlc1 : ∀ y ∈ C, LocallyConnectedAt D₁ y) (hlc2 : ∀ y ∈ C, LocallyConnectedAt D₂ y)
    {z : Plane} (hz : z ∈ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set Plane, IsOpen U ∧ z ∈ U ∧ U ⊆ ball z ε ∧
      IsClosedJordanCurve (frontier U) ∧
      IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
      (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
      (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z) := by
  classical
  -- the two domains avoid the curve
  have hD₁C : Disjoint D₁ C := by
    rw [← hf1, h1o.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  have hD₂C : Disjoint D₂ C := by
    rw [← hf2, h2o.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  have hcover : ∀ w : Plane, w ∈ C ∨ w ∈ D₁ ∨ w ∈ D₂ := by
    intro w
    by_cases hw : w ∈ C
    · exact Or.inl hw
    · have : w ∈ D₁ ∪ D₂ := by rw [hunion]; exact hw
      exact Or.inr this
  -- a cyclic parametrization of the curve
  obtain ⟨Γ, hΓ⟩ := hC.exists_cyclicParam
  obtain ⟨u, hu⟩ : ∃ u, Γ u = z := by rw [← hΓ.range_eq] at hz; exact hz
  -- a point of the curve at positive distance from `z`
  set p₀ : Plane := Γ (u + 1 / 2) with hp₀
  have hp₀C : p₀ ∈ C := by rw [← hΓ.range_eq]; exact mem_range_self _
  have hp₀ne : dist p₀ z ≠ 0 := by
    rw [dist_ne_zero]
    intro hcon
    rw [hp₀, ← hu] at hcon
    obtain ⟨n, hn⟩ := hΓ.inj hcon
    have h1 : (2 : ℝ) * n = -1 := by linarith
    have hn2 : (2 : ℤ) * n = -1 := by exact_mod_cast h1
    omega
  have hp₀pos : 0 < dist p₀ z := lt_of_le_of_ne dist_nonneg (Ne.symm hp₀ne)
  set ε₁ : ℝ := min (ε / 2) (dist p₀ z / 2) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min (by linarith) (by linarith)
  have hε₁ε : ε₁ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hfar : ε₁ < dist p₀ z := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- small crosscuts of the two domains, with prescribed endpoints
  obtain ⟨δ₁, hδ₁, hcross₁⟩ := exists_crosscut_near h1o hf1 hlc1 hz hε₁
  obtain ⟨δ₂, hδ₂, hcross₂⟩ := exists_crosscut_near h2o hf2 hlc2 hz hε₁
  set δ : ℝ := min (min δ₁ δ₂) ε₁ with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) hε₁
  -- a short parameter interval around `u`
  obtain ⟨η, hη, hηlt, hηsub⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 / 4 ∧
      Γ '' Icc (u - η) (u + η) ⊆ ball z δ := by
    have hopen : IsOpen (Γ ⁻¹' ball z δ) := isOpen_ball.preimage hΓ.cont
    have humem : u ∈ Γ ⁻¹' ball z δ := by simp [hu, mem_ball_self hδ]
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hopen u humem
    refine ⟨min (r / 2) (1 / 8), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    rintro y ⟨w, hw, rfl⟩
    refine hrsub ?_
    rw [mem_ball, Real.dist_eq, abs_lt]
    have h1 : min (r / 2) (1 / 8) ≤ r / 2 := min_le_left _ _
    constructor <;> [linarith [hw.1]; linarith [hw.2]]
  set s : ℝ := u - η with hs
  set t : ℝ := u + η with ht
  have hst : s < t := by simp only [hs, ht]; linarith
  have hlen : t - s < 1 := by simp only [hs, ht]; linarith
  have hinjI : InjOn Γ (Icc s t) := hΓ.injOn hlen
  set a : Plane := Γ s with hadef
  set b : Plane := Γ t with hbdef
  have haC : a ∈ C := by rw [hadef, ← hΓ.range_eq]; exact mem_range_self _
  have hbC : b ∈ C := by rw [hbdef, ← hΓ.range_eq]; exact mem_range_self _
  have hab : a ≠ b := by
    intro hcon
    have := hinjI (by constructor <;> [rfl; linarith] : s ∈ Icc s t)
      (by constructor <;> [linarith; rfl] : t ∈ Icc s t) hcon
    simp only [hs, ht] at this
    linarith
  have haball : a ∈ ball z δ := hηsub ⟨s, ⟨le_refl _, by linarith⟩, rfl⟩
  have hbball : b ∈ ball z δ := hηsub ⟨t, ⟨by linarith, le_refl _⟩, rfl⟩
  have hda : dist a z < δ := by rwa [mem_ball] at haball
  have hdb : dist b z < δ := by rwa [mem_ball] at hbball
  -- the two arcs of the curve cut out by `a` and `b`
  obtain ⟨g₁, g₂, harc₁, harc₂, h₁₀, h₁₁, h₂₀, h₂₁, himg₁, hCeq, hint⟩ :=
    exists_arc_decomposition_param hΓ hst hlen
  set A₁ : Set Plane := g₁ '' Icc 0 1 with hA₁
  set A₂ : Set Plane := g₂ '' Icc 0 1 with hA₂
  set I₁ : Set Plane := g₁ '' Ioo 0 1 with hI₁
  have hA₁C : A₁ ⊆ C := by rw [← hCeq]; exact subset_union_left
  have hA₂C : A₂ ⊆ C := by rw [← hCeq]; exact subset_union_right
  have hA₁ball : A₁ ⊆ ball z δ := by
    rw [himg₁]
    rintro y ⟨w, hw, rfl⟩
    exact hηsub ⟨w, hw, rfl⟩
  have hI₁A₁ : I₁ ⊆ A₁ := Set.image_mono Ioo_subset_Icc_self
  have hA₁split : A₁ = I₁ ∪ {a, b} := by
    rw [hA₁, hI₁, image_Icc_eq_union_endpoints, h₁₀, h₁₁]
  have hA₂split : A₂ = g₂ '' Ioo 0 1 ∪ {a, b} := by
    rw [hA₂, image_Icc_eq_union_endpoints, h₂₀, h₂₁]
  have habA₂ : a ∈ A₂ ∧ b ∈ A₂ := by
    rw [hA₂split]
    exact ⟨Or.inr (by simp), Or.inr (by simp)⟩
  have hI₁A₂ : Disjoint I₁ A₂ := by
    rw [hA₂split]
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    rcases hw' with h | h
    · exact (Set.disjoint_left.1 hint) hw h
    · have hd := harc₁.image_Ioo_subset_diff hw
      rw [h₁₀, h₁₁] at hd
      exact hd.2 h
  -- `z` lies in the relative interior of the small arc
  have hzA₁ : z ∈ A₁ := by
    rw [himg₁]
    exact ⟨u, ⟨by linarith, by linarith⟩, hu⟩
  have hza : z ≠ a := by
    intro hcon
    have := hinjI (by constructor <;> [linarith; linarith] : u ∈ Icc s t)
      (by constructor <;> [rfl; linarith] : s ∈ Icc s t) (by rw [hu, hcon, hadef])
    simp only [hs] at this
    linarith
  have hzb : z ≠ b := by
    intro hcon
    have := hinjI (by constructor <;> [linarith; linarith] : u ∈ Icc s t)
      (by constructor <;> [linarith; rfl] : t ∈ Icc s t) (by rw [hu, hcon, hbdef])
    simp only [ht] at this
    linarith
  have hzI₁ : z ∈ I₁ := by
    rcases (hA₁split ▸ hzA₁ : z ∈ I₁ ∪ {a, b}) with h | h
    · exact h
    · rcases h with h | h
      · exact absurd h hza
      · exact absurd h hzb
  -- the two crosscuts
  obtain ⟨k₁, hk₁, hk₁₀, hk₁₁, hk₁sub⟩ := hcross₁ a haC b hbC
    (lt_of_lt_of_le hda (le_trans (min_le_left _ _) (min_le_left _ _)))
    (lt_of_lt_of_le hdb (le_trans (min_le_left _ _) (min_le_left _ _))) hab
  obtain ⟨k₂, hk₂, hk₂₀, hk₂₁, hk₂sub⟩ := hcross₂ a haC b hbC
    (lt_of_lt_of_le hda (le_trans (min_le_left _ _) (min_le_right _ _)))
    (lt_of_lt_of_le hdb (le_trans (min_le_left _ _) (min_le_right _ _))) hab
  set K₁ : Set Plane := k₁ '' Icc 0 1 with hK₁
  set K₂ : Set Plane := k₂ '' Icc 0 1 with hK₂
  have hK₁split : K₁ = k₁ '' Ioo 0 1 ∪ {a, b} := by
    rw [hK₁, image_Icc_eq_union_endpoints, hk₁₀, hk₁₁]
  have hK₂split : K₂ = k₂ '' Ioo 0 1 ∪ {a, b} := by
    rw [hK₂, image_Icc_eq_union_endpoints, hk₂₀, hk₂₁]
  have hK₁ball : K₁ ⊆ closedBall z ε₁ := by
    rw [hK₁split]
    rintro w (hw | hw)
    · exact ball_subset_closedBall (hk₁sub hw).2
    · rcases hw with rfl | rfl
      · exact ball_subset_closedBall (ball_subset_ball (min_le_right _ _) haball)
      · exact ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hbball)
  have hK₂ball : K₂ ⊆ closedBall z ε₁ := by
    rw [hK₂split]
    rintro w (hw | hw)
    · exact ball_subset_closedBall (hk₂sub hw).2
    · rcases hw with rfl | rfl
      · exact ball_subset_closedBall (ball_subset_ball (min_le_right _ _) haball)
      · exact ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hbball)
  -- the domains cut off by the two crosscuts
  obtain ⟨Ω₁, Ω₁', hΩ₁o, hΩ₁'o, hΩ₁c, hΩ₁'c, hΩ₁disj, hΩ₁D, hΩ₁'D, hΩ₁K, hΩ₁'K,
    hfΩ₁, hfΩ₁'⟩ :=
    exists_crosscut_domains h1o h2o hdisj hunion hk₁ harc₁ harc₂
      (by rw [hk₁₀, h₁₀]) (by rw [hk₁₁, h₁₁]) (by rw [h₂₀, h₁₀]) (by rw [h₂₁, h₁₁])
      (fun w hw => (hk₁sub hw).1) hCeq hint
  obtain ⟨Ω₂, Ω₂', hΩ₂o, hΩ₂'o, hΩ₂c, hΩ₂'c, hΩ₂disj, hΩ₂D, hΩ₂'D, hΩ₂K, hΩ₂'K,
    hfΩ₂, hfΩ₂'⟩ :=
    exists_crosscut_domains h2o h1o hdisj.symm (by rw [union_comm]; exact hunion)
      hk₂ harc₁ harc₂
      (by rw [hk₂₀, h₁₀]) (by rw [hk₂₁, h₁₁]) (by rw [h₂₀, h₁₀]) (by rw [h₂₁, h₁₁])
      (fun w hw => (hk₂sub hw).1) hCeq hint
  -- the pieces are closed
  have hK₂closed : IsClosed K₂ := (isCompact_Icc.image_of_continuousOn hk₂.cont).isClosed
  have hA₂closed : IsClosed A₂ := (isCompact_Icc.image_of_continuousOn harc₂.cont).isClosed
  -- the two domains are small
  have hp₀out : p₀ ∉ closedBall z ε₁ := by
    simp only [mem_closedBall, not_le]; exact hfar
  have hΩ₁small : Ω₁ ⊆ closedBall z ε₁ := by
    refine subset_closedBall_of_frontier_subset hΩ₁o hε₁ ?_ hp₀out
      (fun h => (Set.disjoint_left.1 hD₁C) (hΩ₁D h) hp₀C)
    rw [hfΩ₁]
    exact union_subset hK₁ball
      (fun w hw => ball_subset_closedBall (ball_subset_ball (min_le_right _ _) (hA₁ball hw)))
  have hΩ₂small : Ω₂ ⊆ closedBall z ε₁ := by
    refine subset_closedBall_of_frontier_subset hΩ₂o hε₁ ?_ hp₀out
      (fun h => (Set.disjoint_left.1 hD₂C) (hΩ₂D h) hp₀C)
    rw [hfΩ₂]
    exact union_subset hK₂ball
      (fun w hw => ball_subset_closedBall (ball_subset_ball (min_le_right _ _) (hA₁ball hw)))
  obtain ⟨U, hUopen, hzU, hUsmall, hJ, hc1, hc2, hacc1, hacc2⟩ :=
    exists_local_nbhd_of_data (C := C) (A₂ := g₂ '' Icc 0 1) (a := a) (b := b) (ε₁ := ε₁)
      h1o h2o hdisj hunion hf1 hf2 hlc1 hlc2 hz harc₁ hk₁ hk₂
      h₁₀ h₁₁ hk₁₀ hk₁₁ hk₂₀ hk₂₁ hk₁sub hk₂sub hA₂closed hCeq hI₁A₂ habA₂
      (fun w hw => ball_subset_ball (min_le_right _ _) (hA₁ball hw)) hzI₁
      hΩ₁o hΩ₁c hΩ₁D hfΩ₁ hΩ₁small hΩ₂o hΩ₂c hΩ₂D hfΩ₂ hΩ₂small
  exact ⟨U, hUopen, hzU, fun w hw => closedBall_subset_ball hε₁ε (hUsmall hw), hJ, hc1, hc2,
    hacc1, hacc2⟩

end AVD
