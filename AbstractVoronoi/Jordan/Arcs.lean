import AbstractVoronoi.Jordan.Sphere

/-!
# Arcs and accessibility

This file contains the notion of *arc* and of *accessibility* used in

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

(see footnote 5 of the paper, and Theorem 4 and Lemma 8 for accessibility).
-/

noncomputable section

open Set Topology

namespace AVD

/-! ## Arcs and accessibility -/

/-- `IsArc γ` says that `γ` restricted to `[0,1]` is an *arc*, i.e. a homeomorphic image of
the unit interval: `γ` is continuous and injective on `[0,1]` (on the compact Hausdorff
interval this is the same as being a homeomorphism onto its image).

This is the notion of arc used throughout Klein–Langetepe–Nilforoushan (2009); see
footnote 5 of the paper. -/
structure IsArc (γ : ℝ → Plane) : Prop where
  cont : ContinuousOn γ (Icc 0 1)
  inj : InjOn γ (Icc 0 1)

/-- `AccessibleWithin A x w` : the point `w` is *accessible from `x` inside `A`*, that is,
there is an arc `α` from `x` to `w` such that `α` minus its endpoint `w` is contained in `A`.
This is the notion of accessibility used in Theorem 4 of
Klein–Langetepe–Nilforoushan (2009). -/
def AccessibleWithin (A : Set Plane) (x w : Plane) : Prop :=
  ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = w ∧ γ '' Ico 0 1 ⊆ A

/-- `AccessibleFrom A w` : the point `w` is *accessible from the set `A`*, i.e. there is an
arc `α` with endpoint `w` such that `α \ {w} ⊆ A`.  This is the notion appearing in
Lemma 8 of Klein–Langetepe–Nilforoushan (2009). -/
def AccessibleFrom (A : Set Plane) (w : Plane) : Prop :=
  ∃ γ : ℝ → Plane, IsArc γ ∧ γ 1 = w ∧ γ '' Ico 0 1 ⊆ A

/-- Accessibility is monotone in the set from which the point is accessed. -/
theorem AccessibleFrom.mono {A B : Set Plane} {w : Plane} (hAB : A ⊆ B)
    (h : AccessibleFrom A w) : AccessibleFrom B w := by
  obtain ⟨γ, harc, h1, hsub⟩ := h
  exact ⟨γ, harc, h1, hsub.trans hAB⟩

/-- A point accessible from a given point inside `A` is accessible from `A`. -/
theorem AccessibleFrom.of_within {A : Set Plane} {x w : Plane}
    (h : AccessibleWithin A x w) : AccessibleFrom A w := by
  obtain ⟨γ, harc, _, h1, hsub⟩ := h
  exact ⟨γ, harc, h1, hsub⟩

/-- The image of an arc is its relative interior together with its two endpoints. -/
theorem image_Icc_eq_union_endpoints {γ : ℝ → Plane} :
    γ '' Icc 0 1 = γ '' Ioo 0 1 ∪ {γ 0, γ 1} := by
  apply Subset.antisymm
  · rintro y ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact Or.inr (by simp [← h0])
    · rcases eq_or_lt_of_le ht.2 with h1 | h1
      · exact Or.inr (by simp [h1])
      · exact Or.inl ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro y (⟨t, ht, rfl⟩ | hy)
    · exact ⟨t, ⟨le_of_lt ht.1, le_of_lt ht.2⟩, rfl⟩
    · rcases hy with rfl | rfl
      · exact ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
      · exact ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩


end AVD
