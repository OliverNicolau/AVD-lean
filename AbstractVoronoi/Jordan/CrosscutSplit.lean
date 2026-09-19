import AbstractVoronoi.Jordan.ThetaCurve
import AbstractVoronoi.Jordan.LocalStructure

/-!
# Splitting a Jordan domain along a crosscut

This file packages the crosscut theorem (`AVD.exists_crosscut_domains`) and the θ-curve
theorem (`AVD.crosscut_exhausts`) into the single statement that is used in the proof of
**Lemma 8** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902:

a crosscut `κ` of a bounded domain `U` whose frontier is a closed Jordan curve cuts `U` into
exactly two domains, each of which is again a bounded domain whose frontier is a closed
Jordan curve containing `κ` (`AVD.exists_crosscut_split`).  This is the situation of
Fig. 8(3) of the paper, where the segment `H` of `J(p,q)` and a piece of `J(p,r)` cut a
neighbourhood `U` of the common point `w` of the two curves into two domains.

The bridge to the Jordan curve theorem is `AVD.exists_exterior_of_frontier_jordan`: a
bounded domain whose frontier is a closed Jordan curve *is* the bounded complementary domain
of that curve, which is the hypothesis under which the two theorems above are stated.
-/

noncomputable section

open Set Topology

namespace AVD

/-- **A non-empty bounded open set whose frontier is a closed Jordan curve is the bounded
complementary domain of that curve.**

More precisely, such a set `U` is connected and there is a second domain `E` — the exterior
of the curve — with `U ∪ E` the complement of `frontier U` and `frontier E = frontier U`.

This is the bridge which allows the crosscut theorem `AVD.exists_crosscut_domains`, the
θ-curve theorem `AVD.crosscut_exhausts` and the local part of Theorem 4 of
Klein–Langetepe–Nilforoushan (2009) to be applied to the neighbourhoods `U` produced by
Theorem 4 itself, and to the domains cut out of them by a crosscut.  The proof is the
observation that `U` is relatively clopen in the complement of its frontier, hence a union
of complementary domains of the curve, and that it can contain neither both of them nor the
unbounded one. -/
theorem exists_exterior_of_frontier_jordan {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty)
    (hbdd : Bornology.IsBounded U) (hJ : IsClosedJordanCurve (frontier U)) :
    ∃ E : Set Plane, IsOpen E ∧ IsConnected U ∧ IsConnected E ∧ Disjoint U E ∧
      U ∪ E = (frontier U)ᶜ ∧ frontier E = frontier U := by
  obtain ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, hf1, hf2, hbd⟩ :=
    hJ.exists_separation_frontier_eq
  have hUsub : U ⊆ (frontier U)ᶜ := fun x hx hxf => (hU.frontier_eq ▸ hxf).2 hx
  have hcover : (frontier U)ᶜ ⊆ U ∪ (closure U)ᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr fun hxc => hx ⟨hxc, by rwa [hU.interior_eq]⟩
  have hdis : Disjoint U ((closure U)ᶜ) :=
    Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
  have hsplit : ∀ D : Set Plane, IsPreconnected D → D ⊆ (frontier U)ᶜ →
      D ⊆ U ∨ D ⊆ (closure U)ᶜ := fun D hD hDsub =>
    hD.subset_or_subset hU isClosed_closure.isOpen_compl hdis (hDsub.trans hcover)
  have h1sub : D₁ ⊆ (frontier U)ᶜ := by rw [← hunion]; exact subset_union_left
  have h2sub : D₂ ⊆ (frontier U)ᶜ := by rw [← hunion]; exact subset_union_right
  -- if `U` contains one of the two domains and misses the other, it is that domain
  have main : ∀ D E : Set Plane, D ∪ E = (frontier U)ᶜ → D ⊆ U → E ⊆ (closure U)ᶜ →
      U = D := by
    intro D E huni hDU hEU
    refine Subset.antisymm (fun x hx => ?_) hDU
    rcases (huni ▸ hUsub hx : x ∈ D ∪ E) with h | h
    · exact h
    · exact absurd (subset_closure hx) (hEU h)
  rcases hsplit D₁ h1c.isPreconnected h1sub with hc1 | hc1 <;>
    rcases hsplit D₂ h2c.isPreconnected h2sub with hc2 | hc2
  · -- both domains inside `U`: then `U` contains the unbounded one
    exfalso
    rcases hbd with ⟨-, h⟩ | ⟨-, h⟩
    · exact h (hbdd.subset hc2)
    · exact h (hbdd.subset hc1)
  · have hUeq : U = D₁ := main D₁ D₂ hunion hc1 hc2
    refine ⟨D₂, h2o, by rw [hUeq]; exact h1c, h2c, by rw [hUeq]; exact hdisj, ?_, hf2⟩
    have h : U ∪ D₂ = D₁ ∪ D₂ := by rw [hUeq]
    rw [h]; exact hunion
  · have hUeq : U = D₂ := main D₂ D₁ (by rw [union_comm]; exact hunion) hc2 hc1
    refine ⟨D₁, h1o, by rw [hUeq]; exact h2c, h1c, by rw [hUeq]; exact hdisj.symm, ?_, hf1⟩
    have h : U ∪ D₁ = D₁ ∪ D₂ := by rw [hUeq, union_comm]
    rw [h]; exact hunion
  · -- neither domain meets `U`, which is impossible since `U` is non-empty
    exfalso
    obtain ⟨x, hx⟩ := hne
    rcases (hunion ▸ hUsub hx : x ∈ D₁ ∪ D₂) with h | h
    · exact (hc1 h) (subset_closure hx)
    · exact (hc2 h) (subset_closure hx)

/-- **A crosscut cuts a Jordan domain into exactly two Jordan domains.**

Let `U` be a non-empty bounded open set whose frontier is a closed Jordan curve, and let `κ`
be a crosscut of `U`: an arc whose two (distinct) endpoints lie on `frontier U` and whose
relative interior lies inside `U`.  Then `U ∖ κ` is the union of two disjoint domains
`Ω₁, Ω₂ ⊆ U`, each of them again having a closed Jordan curve as frontier, and each of these
two frontiers containing the whole crosscut.

This is the form in which the construction of Fig. 8(3) in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009) is used:

> Segment `H`, together with parts of `G⁺` and `∂U`, form a simple Jordan curve encircling a
> domain `D`.

The two halves of the proof are `AVD.exists_crosscut_domains` (the crosscut theorem) and
`AVD.crosscut_exhausts` (the θ-curve theorem); that the frontiers are closed Jordan curves
is `AVD.isClosedJordanCurve_of_arcs`, applied to the crosscut and to the two arcs into which
its endpoints cut `frontier U`. -/
theorem exists_crosscut_split {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty)
    (hbdd : Bornology.IsBounded U) (hJ : IsClosedJordanCurve (frontier U))
    {κ : ℝ → Plane} (hκ : IsArc κ) (hκ0 : κ 0 ∈ frontier U) (hκ1 : κ 1 ∈ frontier U)
    (hκne : κ 0 ≠ κ 1) (hκU : κ '' Ioo 0 1 ⊆ U) :
    ∃ Ω₁ Ω₂ : Set Plane, IsOpen Ω₁ ∧ IsOpen Ω₂ ∧ IsConnected Ω₁ ∧ IsConnected Ω₂ ∧
      Disjoint Ω₁ Ω₂ ∧ Ω₁ ⊆ U ∧ Ω₂ ⊆ U ∧
      IsClosedJordanCurve (frontier Ω₁) ∧ IsClosedJordanCurve (frontier Ω₂) ∧
      κ '' Icc 0 1 ⊆ frontier Ω₁ ∧ κ '' Icc 0 1 ⊆ frontier Ω₂ ∧
      U \ κ '' Icc 0 1 ⊆ Ω₁ ∪ Ω₂ := by
  obtain ⟨E, hEo, hUc, hEc, hUE, hunion, hfE⟩ :=
    exists_exterior_of_frontier_jordan hU hne hbdd hJ
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, h10, h11, h20, h21, hcov, hint⟩ :=
    hJ.exists_arc_decomposition hκ0 hκ1 hκne
  obtain ⟨Ω₁, Ω₂, hΩ1o, hΩ2o, hΩ1c, hΩ2c, hΩdisj, hΩ1U, hΩ2U, -, -, hfr1, hfr2⟩ :=
    exists_crosscut_domains hU hEo hUE hunion hκ hγ₁ hγ₂ h10.symm h11.symm
      (h20.trans h10.symm) (h21.trans h11.symm) hκU hcov hint
  have hγ1fr : γ₁ '' Icc 0 1 ⊆ frontier U := hcov ▸ subset_union_left
  have hγ2fr : γ₂ '' Icc 0 1 ⊆ frontier U := hcov ▸ subset_union_right
  -- the relative interior of the crosscut misses the frontier of `U`
  have hκfr : Disjoint (κ '' Ioo 0 1) (frontier U) :=
    Set.disjoint_left.2 fun x hx hxf => (hU.frontier_eq ▸ hxf).2 (hκU hx)
  have hjordan : ∀ γ : ℝ → Plane, IsArc γ → γ 0 = κ 0 → γ 1 = κ 1 →
      γ '' Icc 0 1 ⊆ frontier U → IsClosedJordanCurve (κ '' Icc 0 1 ∪ γ '' Icc 0 1) := by
    intro γ hγ hγ0 hγ1 hγfr
    refine isClosedJordanCurve_of_arcs hκ hγ hγ0.symm hγ1.symm (Set.disjoint_left.2 ?_)
    rintro x hx ⟨t, ht, rfl⟩
    exact (Set.disjoint_left.1 hκfr) hx (hγfr ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
  have hJ1 : IsClosedJordanCurve (frontier Ω₁) := by
    rw [hfr1]; exact hjordan γ₁ hγ₁ h10 h11 hγ1fr
  have hJ2 : IsClosedJordanCurve (frontier Ω₂) := by
    rw [hfr2]; exact hjordan γ₂ hγ₂ h20 h21 hγ2fr
  -- the θ-curve theorem: the two domains exhaust `U ∖ κ`
  have hKclosed : IsClosed (κ '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hκ.cont).isClosed
  have hCK : ∃ y ∈ frontier U, y ∉ κ '' Icc 0 1 := by
    have hhalf : (1/2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    refine ⟨γ₁ (1/2), hγ1fr ⟨1/2, hhalf, rfl⟩, ?_⟩
    intro hmem
    rw [image_Icc_eq_union_endpoints] at hmem
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact (Set.disjoint_left.1 hκfr) h (hγ1fr ⟨1/2, hhalf, rfl⟩)
    · have := hγ₁.inj hhalf (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by rw [h, h10])
      norm_num at this
    · have := hγ₁.inj hhalf (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by rw [h, h11])
      norm_num at this
  have hlc : ∀ y ∈ frontier U, LocallyConnectedAt U y := fun y hy =>
    jordanCurveLocalConnectedness (frontier U) (Or.inl hJ) U E hU hEo hUc hEc hUE hunion rfl
      hfE y hy
  have hexh : U \ κ '' Icc 0 1 ⊆ Ω₁ ∪ Ω₂ :=
    crosscut_exhausts hU rfl hKclosed (isPreconnected_compl_arc hκ) hCK hlc hΩ1o hΩ2o hΩ1U
      hΩ2U hfr1 hfr2 hcov
  exact ⟨Ω₁, Ω₂, hΩ1o, hΩ2o, hΩ1c, hΩ2c, hΩdisj, hΩ1U, hΩ2U, hJ1, hJ2,
    hfr1 ▸ subset_union_left, hfr2 ▸ subset_union_left, hexh⟩

end AVD
