import AbstractVoronoi.AVD.Branches

/-!
# Lemma 7

**Lemma 7** (i) and (ii) of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi
diagrams revisited*, Computational Geometry 42 (2009) 885–902: two bisecting curves of three
sites cannot touch (i) nor cross (ii) at a point that is accessible from the three Voronoi
regions.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Lemma 7** (i) of Klein–Langetepe–Nilforoushan (2009).

> If `G⁻, G⁺` are contained in the closure of the same half-plane defined by `J(p,q)`, the
> same holds for `F⁻, F⁺` with respect to `J(p,r)`.

Here `f` parametrizes `J(p,q)` and `g` parametrizes `J(p,r)`, both passing through the
common point `w` at time `0`; `F∓` and `G∓` are the branches of these curves before and
after `w`.  The hypotheses `hnd₃`, `hnd₄` are part of the standing non-degeneracy assumption
of the paper (footnote 8, stated just before the case distinction A, B, C, D): none of the
segments `F⁻, F⁺` is contained in `J(p,r)`.  The remaining two conditions of that footnote
(none of `G⁻, G⁺` is contained in `J(p,q)`) turn out not to be needed. -/
theorem lemma7_touching (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hnd₃ : ¬ BranchBefore f (C.J p r)) (hnd₄ : ¬ BranchAfter f (C.J p r))
    (hG : (BranchBefore g (closure (C.D p q)) ∧ BranchAfter g (closure (C.D p q))) ∨
          (BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D q p)))) :
    (BranchBefore f (closure (C.D p r)) ∧ BranchAfter f (closure (C.D p r))) ∨
      (BranchBefore f (closure (C.D r p)) ∧ BranchAfter f (closure (C.D r p))) := by
  have hwJ : w ∈ C.J p q := by
    rw [← hf.2, ← hf.1.2.2.1]
    exact mem_range_self 0
  -- points of `J(p,q)` arbitrarily close to `w` inside a half-plane of `J(p,r)`
  have hptb : ∀ X Y : ι, X ∈ S → Y ∈ S → X ≠ Y → C.J X Y = C.J p r →
      BranchBefore f (closure (C.D X Y)) →
      ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.J p q ∧ z ∈ C.D X Y := by
    intro X Y hX hY hXY hJ hA V hV
    obtain ⟨c, -, h1, h2, h3⟩ := exists_point_before hf.1.1 hA hnd₃ (by rw [hf.2]; exact hV)
    refine ⟨f c, h3, by rw [← hf.1.2.2.1]; exact mem_range_self c, ?_⟩
    rw [closure_D_eq hadm hX hY hXY] at h1
    rcases h1 with h | h
    · exact h
    · exact absurd (hJ ▸ h) h2
  have hpta : ∀ X Y : ι, X ∈ S → Y ∈ S → X ≠ Y → C.J X Y = C.J p r →
      BranchAfter f (closure (C.D X Y)) →
      ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.J p q ∧ z ∈ C.D X Y := by
    intro X Y hX hY hXY hJ hA V hV
    obtain ⟨c, -, h1, h2, h3⟩ := exists_point_after hf.1.1 hA hnd₄ (by rw [hf.2]; exact hV)
    refine ⟨f c, h3, by rw [← hf.1.2.2.1]; exact mem_range_self c, ?_⟩
    rw [closure_D_eq hadm hX hY hXY] at h1
    rcases h1 with h | h
    · exact h
    · exact absurd (hJ ▸ h) h2
  -- the contradiction obtained when `J(p,q)` crosses `J(p,r)` at `w`
  have hmain : (∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.J p q ∧ z ∈ C.D p r) →
      (∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.J p q ∧ z ∈ C.D r p) → False := by
    intro hz hz'
    rcases hG with ⟨hGb, hGa⟩ | ⟨hGb, hGa⟩
    · refine not_crossing_aux hadm hp hr hq hp (Ne.symm hpq) hpr hg
        (by rw [C.J_symm hq hp (Ne.symm hpq)]; exact hwJ) hGb hGa ?_ ?_
      · intro V hV
        obtain ⟨z, h1, h2, h3⟩ := hz V hV
        exact ⟨z, h1, by rw [C.J_symm hq hp (Ne.symm hpq)]; exact h2, h3⟩
      · intro V hV
        obtain ⟨z, h1, h2, h3⟩ := hz' V hV
        exact ⟨z, h1, by rw [C.J_symm hq hp (Ne.symm hpq)]; exact h2, h3⟩
    · exact not_crossing_aux hadm hp hr hp hq hpq hpr hg hwJ hGb hGa hz hz'
  obtain ⟨hFb, hFa⟩ := branch_dichotomy hadm hp hq hr hpq hqr hpr hf.1
  rcases hFb with hFb | hFb <;> rcases hFa with hFa | hFa
  · exact Or.inl ⟨hFb, hFa⟩
  · exact absurd (hmain (hptb p r hp hr hpr rfl hFb)
      (hpta r p hr hp (Ne.symm hpr) (C.J_symm hr hp (Ne.symm hpr)) hFa)) not_false
  · exact absurd (hmain (hpta p r hp hr hpr rfl hFa)
      (hptb r p hr hp (Ne.symm hpr) (C.J_symm hr hp (Ne.symm hpr)) hFb)) not_false
  · exact Or.inr ⟨hFb, hFa⟩

/-- **Lemma 7** (ii) of Klein–Langetepe–Nilforoushan (2009).

> If `F⁻ ⊆ closure (D(p,r))` and `F⁺ ⊆ closure (D(r,p))` then `G⁻ ⊆ closure (D(q,p))` and
> `G⁺ ⊆ closure (D(p,q))`.  The same holds with `+` and `−` reversed.

In other words, if `J(p,q)` crosses `J(p,r)` at `w`, then `J(p,r)` crosses `J(p,q)` at `w`.
The paper fixes which of the two crossing patterns occurs by its orientation convention
("`D(p,r)` lies on the right hand side of `J(p,r)` as `t` tends to `+∞`"); since that
convention is not formalised here, the conclusion is stated in the orientation-free form:
the two branches `G⁻, G⁺` lie in the closures of *different* half-planes of `J(p,q)`, which
is exactly the assertion of the lemma together with its "`+` and `−` reversed" variant.
As in part (i), `hnd₃`, `hnd₄` are the non-degeneracy assumption of footnote 8 of the paper
for the two branches of `J(p,q)`; the corresponding conditions for `J(p,r)` are not needed.
-/
theorem lemma7_crossing (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hnd₃ : ¬ BranchBefore f (C.J p r)) (hnd₄ : ¬ BranchAfter f (C.J p r))
    (hF : BranchBefore f (closure (C.D p r)) ∧ BranchAfter f (closure (C.D r p))) :
    (BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D p q))) ∨
      (BranchBefore g (closure (C.D p q)) ∧ BranchAfter g (closure (C.D q p))) := by
  -- the branches of `f` lie in the closures of *different* half-planes of `J(p,r)`
  have hFdiff : ¬ ((BranchBefore f (closure (C.D p r)) ∧ BranchAfter f (closure (C.D p r))) ∨
      (BranchBefore f (closure (C.D r p)) ∧ BranchAfter f (closure (C.D r p)))) := by
    rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · obtain ⟨c, -, h3, h4, -⟩ :=
        exists_point_after hf.1.1 (h2.inter hF.2) hnd₄ (Filter.univ_mem)
      rw [closure_D_eq hadm hp hr hpr] at h3
      rw [closure_D_eq hadm hr hp (Ne.symm hpr)] at h3
      rcases h3.1 with hA | hA
      · rcases h3.2 with hB | hB
        · exact (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) hA hB
        · exact h4 (by rw [← C.J_symm hr hp (Ne.symm hpr)]; exact hB)
      · exact h4 hA
    · obtain ⟨c, -, h3, h4, -⟩ :=
        exists_point_before hf.1.1 (h1.inter hF.1) hnd₃ (Filter.univ_mem)
      rw [closure_D_eq hadm hr hp (Ne.symm hpr)] at h3
      rw [closure_D_eq hadm hp hr hpr] at h3
      rcases h3.2 with hA | hA
      · rcases h3.1 with hB | hB
        · exact (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) hA hB
        · exact h4 (by rw [← C.J_symm hr hp (Ne.symm hpr)]; exact hB)
      · exact h4 hA
  -- hence, by Lemma 7 (i), the branches of `g` cannot lie in the closure of one half-plane
  have hGdiff : ¬ ((BranchBefore g (closure (C.D p q)) ∧ BranchAfter g (closure (C.D p q))) ∨
      (BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D q p)))) := fun hG =>
    hFdiff (lemma7_touching hadm hp hq hr hpq hqr hpr hf hg hnd₃ hnd₄ hG)
  obtain ⟨hGb, hGa⟩ := branch_dichotomy hadm hp hr hq hpr (Ne.symm hqr) hpq hg.1
  rcases hGb with hGb | hGb <;> rcases hGa with hGa | hGa
  · exact absurd (Or.inl ⟨hGb, hGa⟩) hGdiff
  · exact Or.inr ⟨hGb, hGa⟩
  · exact Or.inl ⟨hGb, hGa⟩
  · exact absurd (Or.inr ⟨hGb, hGa⟩) hGdiff

end CurveSystem

end AVD
