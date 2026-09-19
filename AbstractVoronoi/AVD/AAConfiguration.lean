import AbstractVoronoi.AVD.SharedSegment

/-!
# Configuration AA of Fig. 7 in the proof of Lemma 8, and the case analysis

This file completes the case analysis of the proof of **Lemma 8** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

at a point `w` lying on both bisecting curves `J(p,q)` and `J(p,r)`.

The configurations in which a crosscut of a Theorem 4 neighbourhood of `w` avoiding the two
half-planes `D(q,p)` and `D(r,p)` can be built are settled in
`AbstractVoronoi.AVD.BCConfiguration`; they all require that points of `D(q,p) ∩ D(r,p)`
occur arbitrarily close to `w`.  What is treated here is the opposite situation, in which
the two curves bound only *three* quadrants near `w`: this is configuration **AA** of
Fig. 7 of the paper.

The main result is `AVD.CurveSystem.lemma8_three_quadrants`: in that situation both branches
of each curve lie in the closure of the half-plane of the other one labelled by `p` — that
*is* configuration AA — and, if moreover no branch of one curve is contained in the other
curve (the non-degeneracy assumption of footnote 8 of the paper), the branches even lie in
the *open* half-planes, so that `AVD.CurveSystem.aa_configuration_impossible` applies and
the configuration is impossible.  The touchings of Fig. 5 are excluded here by the
separation lemma `AVD.CurveSystem.exists_branch_disjoint`, applied to all four pairs of
branches.

The degenerate situation — three quadrants *and* a shared segment — is
`AVD.CurveSystem.lemma8_shared_segment`, which reduces it to the results of
`AbstractVoronoi.AVD.SharedSegment`.
-/

noncomputable section

open Set Topology

namespace AVD

/-- A branch contained in a set is contained in any larger set. -/
theorem BranchBefore.mono {γ : ℝ → Plane} {A B : Set Plane} (hAB : A ⊆ B)
    (h : BranchBefore γ A) : BranchBefore γ B := by
  obtain ⟨δ, hδ, hsub⟩ := h
  exact ⟨δ, hδ, hsub.trans hAB⟩

/-- A branch contained in a set is contained in any larger set. -/
theorem BranchAfter.mono {γ : ℝ → Plane} {A B : Set Plane} (hAB : A ⊆ B)
    (h : BranchAfter γ A) : BranchAfter γ B := by
  obtain ⟨δ, hδ, hsub⟩ := h
  exact ⟨δ, hδ, hsub.trans hAB⟩

/-- The branch after the base point of the reversed parametrization is the branch before the
base point of the original one. -/
theorem branchBefore_of_branchAfter_rev {γ : ℝ → Plane} {A : Set Plane}
    (h : BranchAfter (fun t => γ (-t)) A) : BranchBefore γ A := by
  obtain ⟨δ, hδ, hsub⟩ := h
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hsub ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩

/-- The image of the branch before the base point of a reversed parametrization. -/
theorem image_Ioo_rev {γ : ℝ → Plane} {δ : ℝ} :
    (fun t => γ (-t)) '' Ioo (-δ) 0 = γ '' Ioo 0 δ := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **The fourth quadrant at `w`.**

If the branch of `J(p,q)` after `w` lies in the closure of the half-plane `D(r,p)` and is
not contained in the curve `J(p,r)`, then points of `D(q,p) ∩ D(r,p)` occur arbitrarily
close to `w`.

Indeed, such a branch has points `f t` arbitrarily close to `w` lying in the *open*
half-plane `D(r,p)`; each of them lies on `J(p,q)`, which is the frontier of `D(q,p)`
(Theorem 4 of Klein–Langetepe–Nilforoushan (2009)), so every neighbourhood of `f t` — in
particular a small one inside `D(r,p)` — contains points of `D(q,p)`.

This is the hypothesis `hfourth` of the crosscut construction of Fig. 8(3)
(`AVD.CurveSystem.access_of_crosscut`), which distinguishes the configurations BC, AD and DD
from configuration AA of Fig. 7. -/
theorem fourth_quadrant_of_branch (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane} {f : ℝ → Plane}
    (hf : IsProperLineParamAt f (C.J p q) w)
    (hFa : BranchAfter f (closure (C.D r p))) (hnd : ¬ BranchAfter f (C.J p r)) :
    ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p := by
  intro V hV
  obtain ⟨V', hV'V, hV'open, hwV'⟩ := mem_nhds_iff.1 hV
  obtain ⟨δ, hδ, hsub⟩ := hFa
  have hpre : f ⁻¹' V' ∈ 𝓝 (0 : ℝ) :=
    hf.1.1.continuousAt.preimage_mem_nhds (by rw [hf.2]; exact hV'open.mem_nhds hwV')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨t, ht, htn⟩ := exists_notMem_of_not_branchAfter hnd (min ε δ) (lt_min hε hδ)
  have htV : f t ∈ V' := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact lt_of_lt_of_le ht.2 (min_le_left ε δ)
  have hfr : f t ∈ C.D r p := by
    have h1 : f t ∈ closure (C.D r p) :=
      hsub ⟨t, ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right ε δ)⟩, rfl⟩
    rw [closure_D_eq hadm hr hp (Ne.symm hpr)] at h1
    rcases h1 with h | h
    · exact h
    · exact absurd (show f t ∈ C.J p r by rw [C.J_symm hp hr hpr]; exact h) htn
  have hJ : f t ∈ C.J p q := by rw [← hf.1.2.2.1]; exact mem_range_self t
  have hcl : f t ∈ closure (C.D q p) :=
    mem_closure_D_of_mem_J hadm hq hp (Ne.symm hpq)
      (by rw [← C.J_symm hp hq hpq]; exact hJ)
  obtain ⟨z, hz⟩ := mem_closure_iff.1 hcl (V' ∩ C.D r p)
    (hV'open.inter (C.D_isOpen r hr p hp (Ne.symm hpr))) ⟨htV, hfr⟩
  exact ⟨z, hV'V hz.1.1, hz.2, hz.1.2⟩

/-- **In configuration AA the branches lie in the open half-planes.**

If both branches of `J(p,q)` at `w` lie in the closure of `D(p,r)`, if the branch `G⁺` of
`J(p,r)` after `w` lies in the closure of `D(p,q)` and if `G⁺` is not contained in `J(p,q)`
(the non-degeneracy assumption of footnote 8 of Klein–Langetepe–Nilforoushan (2009)), then
`G⁺` lies in the *open* half-plane `D(p,q)`.

In other words, the touchings of Fig. 5 of the paper — the points where a branch of one
curve meets the other curve, which may accumulate at `w` — do not occur in configuration
AA.  The reason is the separation lemma `AVD.CurveSystem.exists_branch_disjoint`, which is
applicable to the pair `(F⁻, G⁺)` and, after reversing the parametrization of `J(p,q)`, to
the pair `(F⁺, G⁺)` as well: near `w` the branch `G⁺` meets neither of the two branches of
`J(p,q)`, and a proper parametrization of `J(p,q)` has no other points near `w`
(`AVD.IsProperLineParam.exists_nbhd`). -/
theorem branchAfter_D_of_nondegenerate (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hFb : BranchBefore f (closure (C.D p r))) (hFa : BranchAfter f (closure (C.D p r)))
    (hGa : BranchAfter g (closure (C.D p q))) (hnd : ¬ BranchAfter g (C.J p q)) :
    BranchAfter g (C.D p q) := by
  have hndG := exists_notMem_of_not_branchAfter hnd
  obtain ⟨δ1, hδ1, δ2, hδ2, hdisj1⟩ :=
    exists_branch_disjoint hadm hp hq hr hpq hqr hpr hf hg hFb hGa hndG
  obtain ⟨δ3, hδ3, δ4, hδ4, hdisj2⟩ :=
    exists_branch_disjoint hadm hp hq hr hpq hqr hpr hf.rev hg hFa.rev hGa hndG
  rw [image_Ioo_rev] at hdisj2
  obtain ⟨W, hWopen, hwW, hWsub⟩ := hf.1.exists_nbhd (show (0 : ℝ) < min δ2 δ4 from
    lt_min hδ2 hδ4)
  rw [hf.2] at hwW
  have hpre : g ⁻¹' W ∈ 𝓝 (0 : ℝ) :=
    hg.1.1.continuousAt.preimage_mem_nhds (by rw [hg.2]; exact hWopen.mem_nhds hwW)
  obtain ⟨δ6, hδ6, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨δG, hδG, hGsub⟩ := hGa
  refine ⟨min (min δ1 δ3) (min δ6 δG), lt_min (lt_min hδ1 hδ3) (lt_min hδ6 hδG), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have ht1 : t < δ1 := lt_of_lt_of_le ht.2 ((min_le_left _ _).trans (min_le_left δ1 δ3))
  have ht3 : t < δ3 := lt_of_lt_of_le ht.2 ((min_le_left _ _).trans (min_le_right δ1 δ3))
  have ht6 : t < δ6 := lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_left δ6 δG))
  have htG : t < δG := lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_right δ6 δG))
  have h1 : g t ∈ closure (C.D p q) := hGsub ⟨t, ⟨ht.1, htG⟩, rfl⟩
  rw [closure_D_eq hadm hp hq hpq] at h1
  rcases h1 with h | h
  · exact h
  exfalso
  have htW : g t ∈ W := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]
    exact ht6
  obtain ⟨s, hs, hst⟩ := hWsub ⟨h, htW⟩
  rcases lt_trichotomy s 0 with hsneg | hs0 | hspos
  · exact (Set.disjoint_left.1 hdisj1) ⟨t, ⟨ht.1, ht1⟩, rfl⟩
      ⟨s, ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δ2 δ4)) hs.1, hsneg⟩, hst⟩
  · have : t = 0 := hg.1.2.1 (by rw [← hst, hs0, hf.2, ← hg.2])
    linarith [ht.1]
  · exact (Set.disjoint_left.1 hdisj2) ⟨t, ⟨ht.1, ht3⟩, rfl⟩
      ⟨s, ⟨hspos, lt_of_lt_of_le hs.2 (min_le_right δ2 δ4)⟩, hst⟩

/-- **The degenerate configurations of the proof of Lemma 8** of
Klein–Langetepe–Nilforoushan (2009): the two bisecting curves are in the configuration
**AA** of Fig. 7 — each branch of each curve lies in the closure of the half-plane of the
other curve labelled by `p` — *and* they share a segment at `w`, that is, a branch of one of
them is contained in the other one.

These are the situations excluded by footnote 8 of the paper, which the paper disposes of in
the discussion preceding Lemma 8 by reducing them to AD, DD and BC through the orientation
conventions of Fig. 7.  Here they are settled directly, and without any orientation
convention, in `AbstractVoronoi.AVD.SharedSegment`: after reversing the parametrizations and
exchanging the roles of `q` and `r` — which is what the four cases below do — the shared
branch may be assumed to be the branch `G⁺` of `J(p,r)`, and
`AVD.CurveSystem.shared_branch_access` applies.  Note that the hypothesis of the paper's
configuration AA that the quadrant `D(q,p) ∩ D(r,p)` be empty near `w` is *not* needed. -/
theorem lemma8_shared_segment (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    (hwq : w ∈ C.J p q) (hwr : w ∈ C.J p r) (hw : w ∈ frontier (C.VR p {p, q, r}))
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hFb : BranchBefore f (closure (C.D p r))) (hFa : BranchAfter f (closure (C.D p r)))
    (hGb : BranchBefore g (closure (C.D p q))) (hGa : BranchAfter g (closure (C.D p q)))
    (hshared : BranchBefore g (C.J p q) ∨ BranchAfter g (C.J p q) ∨
      BranchBefore f (C.J p r) ∨ BranchAfter f (C.J p r)) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hset : ({p, r, q} : Finset ι) = ({p, q, r} : Finset ι) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rcases hshared with h | h | h | h
  · exact shared_branch_access hadm hp hq hr hpq hqr hpr hwq hw hf hg.rev hFb hFa hGa.rev
      h.rev
  · exact shared_branch_access hadm hp hq hr hpq hqr hpr hwq hw hf hg hFb hFa hGb h
  · have hacc := shared_branch_access hadm hp hr hq hpr (Ne.symm hqr) hpq hwr
      (by rw [hset]; exact hw) hg hf.rev hGb hGa hFa.rev h.rev
    rwa [hset] at hacc
  · have hacc := shared_branch_access hadm hp hr hq hpr (Ne.symm hqr) hpq hwr
      (by rw [hset]; exact hw) hg hf hGb hGa hFb h
    rwa [hset] at hacc

/-- **Configuration AA of Fig. 7 in the proof of Lemma 8** of
Klein–Langetepe–Nilforoushan (2009): the case in which the two curves bound only three
quadrants at `w`, i.e. in which the quadrant `D(q,p) ∩ D(r,p)` is empty near `w`.

The proof first shows that this situation *is* configuration AA, that is, that both branches
of each of the two curves lie in the closure of the half-plane of the other one labelled by
`p`: a branch on the other side which is not contained in the other curve would produce
points of `D(q,p) ∩ D(r,p)` arbitrarily close to `w`
(`AVD.CurveSystem.fourth_quadrant_of_branch`), and a branch contained in the other curve
lies in the closures of *both* its half-planes.

In configuration AA the branches then lie in the *open* half-planes
(`AVD.CurveSystem.branchAfter_D_of_nondegenerate`) as soon as no branch of one curve is
contained in the other one, and `AVD.CurveSystem.aa_configuration_impossible` shows that
this is impossible.  The remaining case — three quadrants together with a shared segment at
`w` — is settled by `AVD.CurveSystem.lemma8_shared_segment`. -/
theorem lemma8_three_quadrants (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    (hwq : w ∈ C.J p q) (hwr : w ∈ C.J p r) (hw : w ∈ frontier (C.VR p {p, q, r}))
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hnotAA : ¬ ((BranchBefore g (C.D p q) ∧ BranchAfter g (C.D p q)) ∧
      (BranchBefore f (C.D p r) ∨ BranchAfter f (C.D p r))))
    (hthree : ¬ ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  -- the curves are contained in the closures of the half-planes of one another
  have hJqcl : C.J p q ⊆ closure (C.D p q) := fun x hx =>
    mem_closure_D_of_mem_J hadm hp hq hpq hx
  have hJrcl : C.J p r ⊆ closure (C.D p r) := fun x hx =>
    mem_closure_D_of_mem_J hadm hp hr hpr hx
  obtain ⟨hFb0, hFa0⟩ := branch_dichotomy hadm hp hq hr hpq hqr hpr hf.1
  obtain ⟨hGb0, hGa0⟩ := branch_dichotomy hadm hp hr hq hpr (Ne.symm hqr) hpq hg.1
  -- both branches of `J(p,q)` lie in the closure of `D(p,r)`
  have hFa : BranchAfter f (closure (C.D p r)) := by
    rcases hFa0 with h | h
    · exact h
    · by_cases hnd : BranchAfter f (C.J p r)
      · exact hnd.mono hJrcl
      · exact absurd (fourth_quadrant_of_branch hadm hp hq hr hpq hpr hf h hnd) hthree
  have hFb : BranchBefore f (closure (C.D p r)) := by
    rcases hFb0 with h | h
    · exact h
    · by_cases hnd : BranchBefore f (C.J p r)
      · exact hnd.mono hJrcl
      · refine absurd (fourth_quadrant_of_branch hadm hp hq hr hpq hpr hf.rev h.rev ?_) hthree
        exact fun hcon => hnd (branchBefore_of_branchAfter_rev hcon)
  -- both branches of `J(p,r)` lie in the closure of `D(p,q)`
  have hGa : BranchAfter g (closure (C.D p q)) := by
    rcases hGa0 with h | h
    · exact h
    · by_cases hnd : BranchAfter g (C.J p q)
      · exact hnd.mono hJqcl
      · refine absurd (fun V hV => ?_) hthree
        obtain ⟨z, hzV, hz⟩ := fourth_quadrant_of_branch hadm hp hr hq hpr hpq hg h hnd V hV
        exact ⟨z, hzV, hz.2, hz.1⟩
  have hGb : BranchBefore g (closure (C.D p q)) := by
    rcases hGb0 with h | h
    · exact h
    · by_cases hnd : BranchBefore g (C.J p q)
      · exact hnd.mono hJqcl
      · refine absurd (fun V hV => ?_) hthree
        obtain ⟨z, hzV, hz⟩ :=
          fourth_quadrant_of_branch hadm hp hr hq hpr hpq hg.rev h.rev
            (fun hcon => hnd (branchBefore_of_branchAfter_rev hcon)) V hV
        exact ⟨z, hzV, hz.2, hz.1⟩
  -- either the two curves share a segment at `w`, or configuration AA is impossible
  by_cases hshared : BranchBefore g (C.J p q) ∨ BranchAfter g (C.J p q) ∨
      BranchBefore f (C.J p r) ∨ BranchAfter f (C.J p r)
  · exact lemma8_shared_segment hadm hp hq hr hpq hqr hpr hwq hwr hw hf hg hFb hFa hGb hGa
      hshared
  · exfalso
    push Not at hshared
    obtain ⟨hnGb, hnGa, hnFb, hnFa⟩ := hshared
    -- the branches of `J(p,r)` lie in the open half-plane `D(p,q)`
    have hGaopen : BranchAfter g (C.D p q) :=
      branchAfter_D_of_nondegenerate hadm hp hq hr hpq hqr hpr hf hg hFb hFa hGa hnGa
    have hGbopen : BranchBefore g (C.D p q) := by
      refine branchBefore_of_branchAfter_rev
        (branchAfter_D_of_nondegenerate hadm hp hq hr hpq hqr hpr hf hg.rev hFb hFa hGb.rev
          ?_)
      exact fun hcon => hnGb (branchBefore_of_branchAfter_rev hcon)
    -- and the branch `F⁺` of `J(p,q)` lies in the open half-plane `D(p,r)`
    have hFaopen : BranchAfter f (C.D p r) :=
      branchAfter_D_of_nondegenerate hadm hp hr hq hpr (Ne.symm hqr) hpq hg hf hGb hGa hFa
        hnFa
    exact hnotAA ⟨⟨hGbopen, hGaopen⟩, Or.inr hFaopen⟩

/-- The configurations of Fig. 7 in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009) which are not settled by
`AVD.CurveSystem.lemma8_of_branches`: neither curve stays, near `w`, in the closure of the
half-plane of the other one *not* labelled by `p`.

The case distinction is the following.  If the quadrant `D(q,p) ∩ D(r,p)` is empty near `w`,
this is the configuration AA of Fig. 7, possibly with touchings or with a shared segment,
which is `AVD.CurveSystem.lemma8_three_quadrants`.  Otherwise a crosscut of a Theorem 4
neighbourhood of `w` avoiding both `D(q,p)` and `D(r,p)` can be built out of the branches of
the two curves at `w`, and
`AVD.CurveSystem.access_of_crosscut` produces the access arc; which branches are used
depends on the configuration:

* if both branches of `J(p,q)` at `w` lie in `closure (D(p,r))` (case A for `F`), the whole
  piece of `J(p,q)` inside the neighbourhood is such a crosscut
  (`AVD.CurveSystem.access_of_both_branches_f`);
* if both branches of `J(p,r)` at `w` lie in `closure (D(p,q))` (case A for `G`), the whole
  piece of `J(p,r)` is (`AVD.CurveSystem.access_of_both_branches_g`);
* otherwise the branches of each of the two curves lie in the closures of *different*
  half-planes of the other one, which is configuration BC, and the crosscut of Fig. 8(3) is
  built from the branch `F⁻` of `J(p,q)` on the `p`-side of `J(p,r)` and the branch `G⁺` of
  `J(p,r)` on the `p`-side of `J(p,q)` (`AVD.CurveSystem.bc_configuration_access`).  In that
  last case the non-degeneracy assumption of footnote 8 of the paper is automatic: if the
  branch `G⁺` were contained in `J(p,q)`, it would lie in `closure (D(q,p))` as well, and
  both branches of `J(p,r)` would lie in `closure (D(q,p))`, contrary to the hypothesis
  `hGnot`. -/
theorem lemma8_common_point_crossing (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    (hwq : w ∈ C.J p q) (hwr : w ∈ C.J p r) (hw : w ∈ frontier (C.VR p {p, q, r}))
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hGnot : ¬ (BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D q p))))
    (hFnot : ¬ (BranchBefore f (closure (C.D r p)) ∧ BranchAfter f (closure (C.D r p))))
    (hnotAA : ¬ ((BranchBefore g (C.D p q) ∧ BranchAfter g (C.D p q)) ∧
      (BranchBefore f (C.D p r) ∨ BranchAfter f (C.D p r)))) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  by_cases hfourth : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p
  · by_cases hFA : BranchBefore f (closure (C.D p r)) ∧ BranchAfter f (closure (C.D p r))
    · exact access_of_both_branches_f hadm hp hq hr hpq hpr hf hg hFA.1 hFA.2 hfourth
    · by_cases hGA : BranchBefore g (closure (C.D p q)) ∧ BranchAfter g (closure (C.D p q))
      · exact access_of_both_branches_g hadm hp hq hr hpq hpr hf hg hGA.1 hGA.2 hfourth
      · -- configuration BC: the branches of each curve lie on different sides of the other
        obtain ⟨hGb, hGa⟩ := branch_dichotomy hadm hp hr hq hpr (Ne.symm hqr) hpq hg.1
        obtain ⟨hFb, hFa⟩ := branch_dichotomy hadm hp hq hr hpq hqr hpr hf.1
        -- the branch of `J(p,q)` on the `p`-side of `J(p,r)`, oriented backwards
        have hfchoice : ∃ f' : ℝ → Plane, IsProperLineParamAt f' (C.J p q) w ∧
            BranchBefore f' (closure (C.D p r)) := by
          rcases hFb with h | h
          · exact ⟨f, hf, h⟩
          · rcases hFa with h' | h'
            · exact ⟨fun t => f (-t), hf.rev, h'.rev⟩
            · exact absurd ⟨h, h'⟩ hFnot
        -- the branch of `J(p,r)` on the `p`-side of `J(p,q)`, oriented forwards, together
        -- with its non-degeneracy
        have hJcl : C.J p q ⊆ closure (C.D q p) := fun x hx =>
          mem_closure_D_of_mem_J hadm hq hp (Ne.symm hpq)
            (by rw [← C.J_symm hp hq hpq]; exact hx)
        have hgchoice : ∃ g' : ℝ → Plane, IsProperLineParamAt g' (C.J p r) w ∧
            BranchAfter g' (closure (C.D p q)) ∧
            (∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, g' x ∉ C.J p q) := by
          rcases hGa with h | h
          · refine ⟨g, hg, h, exists_notMem_of_not_branchAfter ?_⟩
            intro hcon
            obtain ⟨δ, hδ, hsub⟩ := hcon
            rcases hGb with hb | hb
            · exact hGA ⟨hb, h⟩
            · exact hGnot ⟨hb, ⟨δ, hδ, hsub.trans hJcl⟩⟩
          · rcases hGb with h' | h'
            · refine ⟨fun t => g (-t), hg.rev, h'.rev, exists_notMem_of_not_branchBefore ?_⟩
              intro hcon
              obtain ⟨δ, hδ, hsub⟩ := hcon
              exact hGnot ⟨⟨δ, hδ, hsub.trans hJcl⟩, h⟩
            · exact absurd ⟨h', h⟩ hGnot
        obtain ⟨f', hf', hFb'⟩ := hfchoice
        obtain ⟨g', hg', hGa', hnd'⟩ := hgchoice
        exact bc_configuration_access hadm hp hq hr hpq hqr hpr hf' hg' hFb' hGa' hnd'
          hfourth
  · exact lemma8_three_quadrants hadm hp hq hr hpq hqr hpr hwq hwr hw hf hg hnotAA hfourth

/-- The main case in the proof of **Lemma 8** of Klein–Langetepe–Nilforoushan (2009): the
boundary point `w` of `VR(p, {p,q,r})` lies on *both* bisecting curves `J(p,q)` and
`J(p,r)`.

This is the case treated in the paper by the analysis of the four configurations AD, DD, AA
and BC of Fig. 7, for which the local structure of the two curves at `w` (Lemma 7) is
combined with the disconnection argument of Lemma 6.  The configurations in which one of
the two curves stays, near `w`, in the closure of the half-plane of the other one *not*
labelled by `p` are settled by `lemma8_of_branches`, and configuration AA in its
non-degenerate form is impossible by `aa_configuration_impossible`; the remaining
configurations are `lemma8_common_point_crossing`. -/
theorem lemma8_common_point (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    (hwq : w ∈ C.J p q) (hwr : w ∈ C.J p r) (hw : w ∈ frontier (C.VR p {p, q, r})) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  obtain ⟨f, hf⟩ := exists_properLineParamAt hadm hp hq hpq hwq
  obtain ⟨g, hg⟩ := exists_properLineParamAt hadm hp hr hpr hwr
  by_cases hGcase : BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D q p))
  · -- both branches of `J(p,r)` stay on the `q`-side of `J(p,q)`
    exact lemma8_of_branches hadm hp hq hr hpq hpr hwq hw hg hGcase.1 hGcase.2
  · by_cases hFcase : BranchBefore f (closure (C.D r p)) ∧ BranchAfter f (closure (C.D r p))
    · -- symmetrically, both branches of `J(p,q)` stay on the `r`-side of `J(p,r)`
      have hset : ({p, q, r} : Finset ι) = {p, r, q} := by rw [Finset.pair_comm q r]
      have h := lemma8_of_branches hadm hp hr hq hpr hpq hwr (by rw [← hset]; exact hw) hf
        hFcase.1 hFcase.2
      rw [← hset] at h
      exact h
    · by_cases hAA : (BranchBefore g (C.D p q) ∧ BranchAfter g (C.D p q)) ∧
          (BranchBefore f (C.D p r) ∨ BranchAfter f (C.D p r))
      · -- configuration AA of Fig. 7 in its non-degenerate form, which is impossible
        exact absurd (aa_configuration_impossible hadm hp hq hr hpq hqr hpr hf hg
          hAA.1.1 hAA.1.2 hAA.2) not_false
      · exact lemma8_common_point_crossing hadm hp hq hr hpq hqr hpr hwq hwr hw hf hg
          hGcase hFcase hAA

end CurveSystem

end AVD
