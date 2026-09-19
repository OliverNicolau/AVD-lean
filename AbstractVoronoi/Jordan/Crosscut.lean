import AbstractVoronoi.Jordan.Accessibility
import AbstractVoronoi.Jordan.ArcFacts

/-!
# Crosscuts of a Jordan domain

A *crosscut* of a complementary domain `D` of a closed Jordan curve `C` is an arc whose two
endpoints lie on `C` and whose relative interior lies in `D`.  Cutting `C` at the two
endpoints of a crosscut `κ` produces two arcs `γ₁`, `γ₂` of `C`, and the two closed curves
`κ ∪ γ₁` and `κ ∪ γ₂` are closed Jordan curves.  The classical *crosscut theorem* says that
`κ` divides `D` into exactly two Jordan domains, bounded by `κ ∪ γ₁` and by `κ ∪ γ₂`.

This file proves, with no assumption, the constructive half of that statement
(`AVD.exists_crosscut_domains`): the two closed Jordan curves
`κ ∪ γ₁` and `κ ∪ γ₂` bound two **disjoint** domains `Ω₁, Ω₂` contained in `D` and disjoint
from `κ`, with `frontier Ωᵢ = κ ∪ γᵢ`.  The remaining half — that `Ω₁` and `Ω₂` exhaust
`D ∖ κ` — is the θ-curve theorem, whose classical proof goes through Janiszewski's theorem
on the union of two closed sets with connected intersection; it is not formalized here.

The file also proves the cutting of a closed Jordan curve at two of its points into two arcs
(`AVD.IsClosedJordanCurve.exists_arc_decomposition`).

Crosscuts are the tool by which the local structure of a Jordan curve — the local part of
**Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902 —

is approached: the neighbourhood `U` of a point `z ∈ C` whose boundary is a closed Jordan
curve is assembled out of crosscuts of the two complementary domains.
-/

noncomputable section

open Set Topology

namespace AVD

/-! ## Cutting a closed Jordan curve at two of its points -/

/-- **A closed Jordan curve is the union of two arcs joining any two of its points.**

Given two distinct points `a`, `b` of a closed Jordan curve `C`, there are two arcs from `a`
to `b` with disjoint relative interiors whose union is `C`.  This is the decomposition used
whenever the paper cuts a bisecting curve at two of its points. -/
theorem IsClosedJordanCurve.exists_arc_decomposition {C : Set Plane}
    (hC : IsClosedJordanCurve C) {a b : Plane} (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ γ₁ γ₂ : ℝ → Plane, IsArc γ₁ ∧ IsArc γ₂ ∧ γ₁ 0 = a ∧ γ₁ 1 = b ∧ γ₂ 0 = a ∧ γ₂ 1 = b ∧
      γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 = C ∧ Disjoint (γ₁ '' Ioo 0 1) (γ₂ '' Ioo 0 1) := by
  obtain ⟨Γ, hΓ⟩ := hC.exists_cyclicParam
  obtain ⟨s, hs⟩ : ∃ s, Γ s = a := by rw [← hΓ.range_eq] at ha; exact ha
  obtain ⟨t, ht, htb⟩ : ∃ t ∈ Icc s (s + 1), Γ t = b := by
    rw [← hΓ.image_Icc s] at hb; obtain ⟨t, ht, htb⟩ := hb; exact ⟨t, ht, htb⟩
  have hts : s < t := by
    rcases lt_or_eq_of_le ht.1 with h | h
    · exact h
    · rw [← h, hs] at htb; exact absurd htb hab
  have hts1 : t < s + 1 := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · rw [h, hΓ.per, hs] at htb; exact absurd htb hab
  -- the two parameter intervals `[s,t]` and `[t,s+1]`
  have key : ∀ c d : ℝ, c < d → d - c < 1 →
      ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = Γ c ∧ γ 1 = Γ d ∧
        γ '' Icc 0 1 = Γ '' Icc c d ∧ γ '' Ioo 0 1 ⊆ Γ '' Ioo c d := by
    intro c d hcd hlen
    have hmem : ∀ x ∈ Icc (0 : ℝ) 1, c + (d - c) * x ∈ Icc c d := by
      intro x hx; constructor <;> nlinarith [hx.1, hx.2]
    have hne : d - c ≠ 0 := by linarith
    refine ⟨fun x => Γ (c + (d - c) * x), ⟨(hΓ.cont.comp (by fun_prop)).continuousOn, ?_⟩,
      by norm_num, by norm_num, ?_, ?_⟩
    · intro x hx y hy hxy
      have h := hΓ.injOn hlen (hmem x hx) (hmem y hy) hxy
      exact mul_left_cancel₀ hne (by linarith)
    · apply Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩; exact ⟨_, hmem x hx, rfl⟩
      · rintro y ⟨u, hu, rfl⟩
        refine ⟨(u - c) / (d - c), ⟨div_nonneg (by linarith [hu.1]) (by linarith),
          by rw [div_le_one (by linarith)]; linarith [hu.2]⟩, ?_⟩
        change Γ (c + (d - c) * ((u - c) / (d - c))) = Γ u
        have hcancel : (d - c) * ((u - c) / (d - c)) = u - c := by field_simp
        rw [hcancel]
        congr 1
        ring
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨_, ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩, rfl⟩
  obtain ⟨γ₁, harc₁, hγ₁0, hγ₁1, himg₁, hIoo₁⟩ := key s t hts (by linarith)
  obtain ⟨δ, harcδ, hδ0, hδ1, himgδ, hIooδ⟩ := key t (s + 1) hts1 (by linarith)
  refine ⟨γ₁, revParam δ, harc₁, harcδ.rev, by rw [hγ₁0, hs], by rw [hγ₁1, htb],
    by rw [revParam_zero, hδ1, hΓ.per, hs], by rw [revParam_one, hδ0, htb], ?_, ?_⟩
  · rw [revParam_image, himg₁, himgδ, hΓ.image_union hts.le hts1.le]
  · rw [revParam_image_Ioo]
    refine Set.disjoint_left.2 fun x hx1 hx2 => ?_
    obtain ⟨u, hu, rfl⟩ := hIoo₁ hx1
    obtain ⟨v, hv, hvu⟩ := hIooδ hx2
    obtain ⟨n, hn⟩ := hΓ.inj hvu
    have hlt : (n : ℝ) < 1 := by rw [← hn]; linarith [hu.2, hv.1]
    have hgt : (-1 : ℝ) < n := by rw [← hn]; linarith [hu.1, hv.2]
    have hlt' : n < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < n := by exact_mod_cast hgt
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    push_cast at hn
    linarith [hu.2, hv.1]

/-! ## The two domains cut off by a crosscut -/

/-- The two complementary domains of a closed Jordan curve, presented so that a prescribed
connected set off the curve lies in the *second* one. -/
theorem IsClosedJordanCurve.exists_separation_avoiding {K S : Set Plane}
    (hK : IsClosedJordanCurve K) (hS : IsPreconnected S) (hSne : S.Nonempty)
    (hSK : Disjoint S K) :
    ∃ Ω Ω' : Set Plane, IsOpen Ω ∧ IsOpen Ω' ∧ IsConnected Ω ∧ IsConnected Ω' ∧
      Disjoint Ω Ω' ∧ Ω ∪ Ω' = Kᶜ ∧ frontier Ω = K ∧ frontier Ω' = K ∧ S ⊆ Ω' := by
  obtain ⟨P, Q, hPo, hQo, hPc, hQc, hdisj, hunion, hfP, hfQ, -⟩ :=
    hK.exists_separation_frontier_eq
  have hSsub : S ⊆ P ∪ Q := by
    rw [hunion]
    intro x hx
    exact Set.disjoint_left.1 hSK hx
  obtain ⟨x, hx⟩ := hSne
  rcases hSsub hx with hxP | hxQ
  · exact ⟨Q, P, hQo, hPo, hQc, hPc, hdisj.symm, by rw [union_comm]; exact hunion, hfQ, hfP,
      hS.subset_left_of_subset_union hPo hQo hdisj hSsub ⟨x, hx, hxP⟩⟩
  · exact ⟨P, Q, hPo, hQo, hPc, hQc, hdisj, hunion, hfP, hfQ,
      hS.subset_right_of_subset_union hPo hQo hdisj hSsub ⟨x, hx, hxQ⟩⟩

/-- **The crosscut theorem for a Jordan domain** (the half proved here).

Let `C` be a closed Jordan curve with complementary domains `D` and `E`, let `κ` be a
*crosscut* of `D` — an arc whose endpoints lie on `C` and whose relative interior lies in
`D` — and let `γ₁`, `γ₂` be the two arcs into which the endpoints of `κ` cut `C`.  Then the
two closed Jordan curves `κ ∪ γ₁` and `κ ∪ γ₂` bound two **disjoint** domains `Ω₁, Ω₂`
contained in `D` and disjoint from `κ`, with `frontier Ωᵢ = κ ∪ γᵢ`.

This is the constructive half of the classical crosscut theorem ("a crosscut divides a
Jordan domain into exactly two Jordan domains"), which underlies the construction of the
neighbourhoods `U` in **Theorem 4** of Klein–Langetepe–Nilforoushan (2009).  That
`Ω₁ ∪ Ω₂` is *all* of `D ∖ κ` is the θ-curve theorem and is not formalized here.

(The hypothesis that `C` is a closed Jordan curve turns out not to be needed: it is implied
by the decomposition of `C` into the two arcs `γ₁`, `γ₂`.) -/
theorem exists_crosscut_domains {C : Set Plane}
    {D E : Set Plane} (hDo : IsOpen D) (hEo : IsOpen E)
    (hdisjDE : Disjoint D E) (hunion : D ∪ E = Cᶜ)
    {κ γ₁ γ₂ : ℝ → Plane} (hκ : IsArc κ) (hγ₁ : IsArc γ₁) (hγ₂ : IsArc γ₂)
    (hκ0 : κ 0 = γ₁ 0) (hκ1 : κ 1 = γ₁ 1) (h20 : γ₂ 0 = γ₁ 0) (h21 : γ₂ 1 = γ₁ 1)
    (hcross : κ '' Ioo 0 1 ⊆ D)
    (hCeq : γ₁ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 = C)
    (hint : Disjoint (γ₁ '' Ioo 0 1) (γ₂ '' Ioo 0 1)) :
    ∃ Ω₁ Ω₂ : Set Plane, IsOpen Ω₁ ∧ IsOpen Ω₂ ∧ IsConnected Ω₁ ∧ IsConnected Ω₂ ∧
      Disjoint Ω₁ Ω₂ ∧ Ω₁ ⊆ D ∧ Ω₂ ⊆ D ∧
      Disjoint Ω₁ (κ '' Icc 0 1) ∧ Disjoint Ω₂ (κ '' Icc 0 1) ∧
      frontier Ω₁ = κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1 ∧
      frontier Ω₂ = κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 := by
  have hDC : Disjoint D C := by
    rw [Set.disjoint_right]
    intro x hxC hxD
    have hx : x ∈ Cᶜ := by rw [← hunion]; exact Or.inl hxD
    exact hx hxC
  have hγ₁C : γ₁ '' Icc 0 1 ⊆ C := by rw [← hCeq]; exact subset_union_left
  have hγ₂C : γ₂ '' Icc 0 1 ⊆ C := by rw [← hCeq]; exact subset_union_right
  have hendκ : κ '' Icc 0 1 ⊆ κ '' Ioo 0 1 ∪ {γ₁ 0, γ₁ 1} := by
    rw [image_Icc_eq_union_endpoints, hκ0, hκ1]
  have hγ₁Ioo : γ₁ '' Ioo 0 1 ⊆ γ₁ '' Icc 0 1 \ {γ₁ 0, γ₁ 1} := hγ₁.image_Ioo_subset_diff
  have hγ₂Ioo : γ₂ '' Ioo 0 1 ⊆ γ₂ '' Icc 0 1 \ {γ₁ 0, γ₁ 1} := by
    have h := hγ₂.image_Ioo_subset_diff
    rwa [h20, h21] at h
  -- the relative interiors of the three arcs are pairwise disjoint from the other arcs
  have hdisj₁κ : Disjoint (γ₁ '' Ioo 0 1) (κ '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun x hx hxκ => ?_
    rcases hendκ hxκ with h | h
    · exact (Set.disjoint_left.1 hDC) (hcross h) (hγ₁C (hγ₁Ioo hx).1)
    · exact (hγ₁Ioo hx).2 h
  have hdisj₂κ : Disjoint (γ₂ '' Ioo 0 1) (κ '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun x hx hxκ => ?_
    rcases hendκ hxκ with h | h
    · exact (Set.disjoint_left.1 hDC) (hcross h) (hγ₂C (hγ₂Ioo hx).1)
    · exact (hγ₂Ioo hx).2 h
  have hdisj₁₂' : Disjoint (γ₁ '' Ioo 0 1) (γ₂ '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun x hx hx2 => ?_
    rw [image_Icc_eq_union_endpoints, h20, h21] at hx2
    rcases hx2 with h | h
    · exact (Set.disjoint_left.1 hint) hx h
    · exact (hγ₁Ioo hx).2 h
  have hdisj₂₁' : Disjoint (γ₂ '' Ioo 0 1) (γ₁ '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun x hx hx1 => ?_
    rw [image_Icc_eq_union_endpoints] at hx1
    rcases hx1 with h | h
    · exact (Set.disjoint_left.1 hint) h hx
    · exact (hγ₂Ioo hx).2 h
  -- the two closed Jordan curves
  have hdisjκ₁ : Disjoint (κ '' Ioo 0 1) (γ₁ '' Ioo 0 1) :=
    Set.disjoint_left.2 fun x hx hx1 =>
      (Set.disjoint_left.1 hDC) (hcross hx) (hγ₁C (hγ₁Ioo hx1).1)
  have hdisjκ₂ : Disjoint (κ '' Ioo 0 1) (γ₂ '' Ioo 0 1) :=
    Set.disjoint_left.2 fun x hx hx2 =>
      (Set.disjoint_left.1 hDC) (hcross hx) (hγ₂C (hγ₂Ioo hx2).1)
  have hK₁ : IsClosedJordanCurve (κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1) :=
    isClosedJordanCurve_of_arcs hκ hγ₁ hκ0 hκ1 hdisjκ₁
  have hK₂ : IsClosedJordanCurve (κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1) :=
    isClosedJordanCurve_of_arcs hκ hγ₂ (by rw [hκ0, h20]) (by rw [hκ1, h21]) hdisjκ₂
  have hne₁ : (γ₁ '' Ioo 0 1).Nonempty := ⟨γ₁ (1/2), 1/2, by norm_num, rfl⟩
  have hne₂ : (γ₂ '' Ioo 0 1).Nonempty := ⟨γ₂ (1/2), 1/2, by norm_num, rfl⟩
  have hmκ : κ (1/2) ∈ κ '' Ioo 0 1 := ⟨1/2, by norm_num, rfl⟩
  have hmκ' : κ (1/2) ∈ κ '' Icc 0 1 := ⟨1/2, by norm_num, rfl⟩
  have hpre₁ : IsPreconnected (γ₁ '' Ioo 0 1) :=
    isPreconnected_Ioo.image γ₁ (hγ₁.cont.mono Ioo_subset_Icc_self)
  have hpre₂ : IsPreconnected (γ₂ '' Ioo 0 1) :=
    isPreconnected_Ioo.image γ₂ (hγ₂.cont.mono Ioo_subset_Icc_self)
  -- the two domains, each taken on the side away from the other arc of `C`
  obtain ⟨Ω₁, P₁, hΩ₁o, hP₁o, hΩ₁c, hP₁c, hd₁, hu₁, hfΩ₁, -, hsub₁⟩ :=
    hK₁.exists_separation_avoiding hpre₂ hne₂
      (Set.disjoint_union_right.2 ⟨hdisj₂κ, hdisj₂₁'⟩)
  obtain ⟨Ω₂, P₂, hΩ₂o, hP₂o, hΩ₂c, hP₂c, hd₂, hu₂, hfΩ₂, -, hsub₂⟩ :=
    hK₂.exists_separation_avoiding hpre₁ hne₁
      (Set.disjoint_union_right.2 ⟨hdisj₁κ, hdisj₁₂'⟩)
  have hΩ₁K₁ : Disjoint Ω₁ (κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1) := by
    rw [Set.disjoint_right]
    intro x hx hxΩ
    have hxc : x ∈ (κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1)ᶜ := by rw [← hu₁]; exact Or.inl hxΩ
    exact hxc hx
  have hΩ₂K₂ : Disjoint Ω₂ (κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1) := by
    rw [Set.disjoint_right]
    intro x hx hxΩ
    have hxc : x ∈ (κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1)ᶜ := by rw [← hu₂]; exact Or.inl hxΩ
    exact hxc hx
  have hendmem : γ₁ 0 ∈ κ '' Icc 0 1 ∧ γ₁ 1 ∈ κ '' Icc 0 1 :=
    ⟨⟨0, ⟨le_refl 0, zero_le_one⟩, hκ0⟩, ⟨1, ⟨zero_le_one, le_refl 1⟩, hκ1⟩⟩
  have hΩ₁γ₂ : Disjoint Ω₁ (γ₂ '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun x hx hx2 => ?_
    rw [image_Icc_eq_union_endpoints, h20, h21] at hx2
    rcases hx2 with h | h
    · exact (Set.disjoint_left.1 hd₁) hx (hsub₁ h)
    · refine (Set.disjoint_left.1 hΩ₁K₁) hx (Or.inl ?_)
      rcases h with rfl | rfl
      · exact hendmem.1
      · exact hendmem.2
  have hΩ₂γ₁ : Disjoint Ω₂ (γ₁ '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun x hx hx1 => ?_
    rw [image_Icc_eq_union_endpoints] at hx1
    rcases hx1 with h | h
    · exact (Set.disjoint_left.1 hd₂) hx (hsub₂ h)
    · refine (Set.disjoint_left.1 hΩ₂K₂) hx (Or.inl ?_)
      rcases h with rfl | rfl
      · exact hendmem.1
      · exact hendmem.2
  have hΩ₁κ : Disjoint Ω₁ (κ '' Icc 0 1) :=
    Set.disjoint_left.2 fun x hx h => (Set.disjoint_left.1 hΩ₁K₁) hx (Or.inl h)
  have hΩ₂κ : Disjoint Ω₂ (κ '' Icc 0 1) :=
    Set.disjoint_left.2 fun x hx h => (Set.disjoint_left.1 hΩ₂K₂) hx (Or.inl h)
  have hΩ₁C : Disjoint Ω₁ C := by
    rw [← hCeq]
    exact Set.disjoint_union_right.2
      ⟨Set.disjoint_left.2 fun x hx h => (Set.disjoint_left.1 hΩ₁K₁) hx (Or.inr h), hΩ₁γ₂⟩
  have hΩ₂C : Disjoint Ω₂ C := by
    rw [← hCeq]
    exact Set.disjoint_union_right.2
      ⟨hΩ₂γ₁, Set.disjoint_left.2 fun x hx h => (Set.disjoint_left.1 hΩ₂K₂) hx (Or.inr h)⟩
  -- both domains lie in `D`, because their boundaries contain the interior of the crosscut
  have hin : ∀ Ω : Set Plane, IsConnected Ω → Disjoint Ω C → κ (1/2) ∈ closure Ω → Ω ⊆ D := by
    intro Ω hΩc hΩC hmcl
    have hΩsub : Ω ⊆ D ∪ E := by
      rw [hunion]
      intro x hx
      exact Set.disjoint_left.1 hΩC hx
    obtain ⟨y, hyD, hyΩ⟩ := mem_closure_iff.1 hmcl D hDo (hcross hmκ)
    exact hΩc.isPreconnected.subset_left_of_subset_union hDo hEo hdisjDE hΩsub ⟨y, hyΩ, hyD⟩
  have hΩ₁D : Ω₁ ⊆ D :=
    hin Ω₁ hΩ₁c hΩ₁C (frontier_subset_closure (by rw [hfΩ₁]; exact Or.inl hmκ'))
  have hΩ₂D : Ω₂ ⊆ D :=
    hin Ω₂ hΩ₂c hΩ₂C (frontier_subset_closure (by rw [hfΩ₂]; exact Or.inl hmκ'))
  -- the two domains are disjoint
  have hdisjΩ : Disjoint Ω₁ Ω₂ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    -- `Ω₂` avoids `κ ∪ γ₁`, hence lies in `Ω₁` or in `P₁`; it meets `Ω₁`, so `Ω₂ ⊆ Ω₁`
    have hΩ₂K₁ : Disjoint Ω₂ (κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1) :=
      Set.disjoint_union_right.2 ⟨hΩ₂κ, hΩ₂γ₁⟩
    have hΩ₂sub : Ω₂ ⊆ Ω₁ ∪ P₁ := by
      rw [hu₁]
      intro y hy
      exact Set.disjoint_left.1 hΩ₂K₁ hy
    have h21' : Ω₂ ⊆ Ω₁ :=
      hΩ₂c.isPreconnected.subset_left_of_subset_union hΩ₁o hP₁o hd₁ hΩ₂sub ⟨x, hx2, hx1⟩
    have hΩ₁K₂ : Disjoint Ω₁ (κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1) :=
      Set.disjoint_union_right.2 ⟨hΩ₁κ, hΩ₁γ₂⟩
    have hΩ₁sub : Ω₁ ⊆ Ω₂ ∪ P₂ := by
      rw [hu₂]
      intro y hy
      exact Set.disjoint_left.1 hΩ₁K₂ hy
    have h12' : Ω₁ ⊆ Ω₂ :=
      hΩ₁c.isPreconnected.subset_left_of_subset_union hΩ₂o hP₂o hd₂ hΩ₁sub ⟨x, hx1, hx2⟩
    have heq : Ω₁ = Ω₂ := Subset.antisymm h12' h21'
    have hKeq : κ '' Icc 0 1 ∪ γ₁ '' Icc 0 1 = κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 := by
      rw [← hfΩ₁, ← hfΩ₂, heq]
    obtain ⟨y, hy⟩ := hne₁
    have hyK : y ∈ κ '' Icc 0 1 ∪ γ₂ '' Icc 0 1 := by
      rw [← hKeq]
      exact Or.inr (Set.image_mono Ioo_subset_Icc_self hy)
    rcases hyK with h | h
    · exact (Set.disjoint_left.1 hdisj₁κ) hy h
    · exact (Set.disjoint_left.1 hdisj₁₂') hy h
  exact ⟨Ω₁, Ω₂, hΩ₁o, hΩ₂o, hΩ₁c, hΩ₂c, hdisjΩ, hΩ₁D, hΩ₂D, hΩ₁κ, hΩ₂κ, hfΩ₁, hfΩ₂⟩

end AVD
