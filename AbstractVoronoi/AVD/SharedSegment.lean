import AbstractVoronoi.AVD.BCConfiguration

/-!
# The degenerate configurations of Lemma 8: two curves sharing a segment

This file treats the configurations of the proof of **Lemma 8** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

in which the two bisecting curves `J(p,q)` and `J(p,r)` *share a segment* at their common
point `w`: a branch of one of them is contained in the other one.  These are the degenerate
situations which footnote 8 of the paper excludes from the discussion of Fig. 7, and which
the paper disposes of by the orientation conventions preceding Lemma 8.

The treatment here is orientation-free and splits into two cases.

* If **both** branches of `J(p,r)` at `w` lie on `J(p,q)` — the two curves coincide near
  `w` — then the piece of `J(p,r)` inside a Theorem 4 neighbourhood of `w` is a crosscut
  lying on *both* curves, so it avoids all four half-planes `D(q,p)`, `D(p,q)`, `D(r,p)` and
  `D(p,r)`.  The two domains it cuts out are therefore unions of the local half-planes, and
  a short argument shows that either the Voronoi region is empty near `w`, contradicting
  `w ∈ frontier (VR p)`, or the construction of Fig. 8(3) applies.  This is
  `AVD.CurveSystem.shared_both_branches_access`.
* If only **one** branch is shared, the crosscut of Fig. 8(3) is built from the *other*
  branch of `J(p,r)` and from a branch of `J(p,q)` which the shared branch avoids, and the
  shared branch itself then supplies a common point of the two curves off the crosscut —
  a joining set in the sense of `AVD.CurveSystem.access_of_crosscut_join`.  This is
  `AVD.CurveSystem.shared_crosscut_access` and `AVD.CurveSystem.shared_branch_access`.
-/

noncomputable section

open Set Topology

namespace AVD

/-- The image under a reversed parametrization of the non-positive half-line is the image of
the non-negative one. -/
theorem image_Iic_rev {γ : ℝ → Plane} : (fun t => γ (-t)) '' Iic 0 = γ '' Ici 0 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp only [mem_Iic] at ht
    exact ⟨-t, by simp only [mem_Ici]; linarith, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    simp only [mem_Ici] at ht
    exact ⟨-t, by simp only [mem_Iic]; linarith, by simp⟩

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- The two complementary domains of a bisecting curve `J(p,q)` provided by the global part
of Theorem 4 of Klein–Langetepe–Nilforoushan (2009) are the two half-planes `D(p,q)` and
`D(q,p)`, in one order or the other.  This refines `AVD.CurveSystem.D_eq_of_separation`,
which identifies only one of them. -/
theorem D_pair_eq_of_separation (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {D₁ D₂ : Set Plane} (hc1 : IsConnected D₁) (hc2 : IsConnected D₂)
    (hd12 : Disjoint D₁ D₂) (hu12 : D₁ ∪ D₂ = (C.J p q)ᶜ) :
    (C.D p q = D₁ ∧ C.D q p = D₂) ∨ (C.D p q = D₂ ∧ C.D q p = D₁) := by
  have hdisjD : Disjoint (C.D p q) (C.D q p) := C.D_disjoint p hp q hq hpq
  have hcover : D₁ ∪ D₂ = C.D p q ∪ C.D q p := by
    rw [hu12, C.compl_J p hp q hq hpq]
  have hkey : ∀ A B : Set Plane, C.D p q = A → A ∪ B = C.D p q ∪ C.D q p →
      Disjoint A B → C.D q p = B := by
    intro A B hA hAB hdisj
    apply Subset.antisymm
    · intro x hx
      have hx' : x ∈ A ∪ B := by rw [hAB]; exact Or.inr hx
      rcases hx' with h' | h'
      · exact absurd hx (Set.disjoint_left.1 hdisjD (by rw [hA]; exact h'))
      · exact h'
    · intro x hx
      have hx' : x ∈ C.D p q ∪ C.D q p := by rw [← hAB]; exact Or.inr hx
      rcases hx' with h' | h'
      · exact absurd hx (Set.disjoint_left.1 hdisj (by rw [← hA]; exact h'))
      · exact h'
  rcases D_eq_of_separation hadm hp hq hpq hc1 hc2 hu12 with h | h
  · exact Or.inl ⟨h, hkey D₁ D₂ h hcover hd12⟩
  · exact Or.inr ⟨h, hkey D₂ D₁ h (by rw [union_comm]; exact hcover) hd12.symm⟩

/-- **Theorem 4** of Klein–Langetepe–Nilforoushan (2009) for a bisecting curve `J(p,q)`, in
the form needed for the degenerate configurations of Lemma 8: the neighbourhood `U` of a
point `z` of the curve is bounded, has a closed Jordan curve as frontier, and meets *both*
half-planes `D(p,q)` and `D(q,p)` in a connected set.

This strengthens `AVD.CurveSystem.exists_theorem4_jordan_nbhd`, which retains only one of
the two connectedness statements of Theorem 4. -/
theorem exists_theorem4_jordan_nbhd_both (hadm : C.Admissible) {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane} (hz : z ∈ C.J p q)
    {V : Set Plane} (hV : V ∈ 𝓝 z) :
    ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧ Bornology.IsBounded U ∧
      IsClosedJordanCurve (frontier U) ∧ IsConnected (U ∩ C.D p q) ∧
      IsConnected (U ∩ C.D q p) := by
  obtain ⟨D₁, D₂, hO1, hO2, hc1, hc2, hd12, hu12, hf1, hf2⟩ :=
    (hadm.A1 p hp q hq hpq).exists_separation_frontier_eq
  have hacc := jordanCurveLocalAccessibility (C.J p q) (Or.inr (hadm.A1 p hp q hq hpq))
    D₁ D₂ hO1 hO2 hc1 hc2 hd12 hu12 hf1 hf2
  have hV' : V ∩ Metric.ball z 1 ∈ 𝓝 z :=
    Filter.inter_mem hV (Metric.ball_mem_nhds z one_pos)
  obtain ⟨U, hUnhds, hUV, hUopen, hJ, hconn1, hconn2, -, -⟩ := hacc z hz _ hV'
  have hbdd : Bornology.IsBounded U :=
    Metric.isBounded_ball.subset fun x hx => (hUV hx).2
  rcases D_pair_eq_of_separation hadm hp hq hpq hc1 hc2 hd12 hu12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨U, hUnhds, fun x hx => (hUV hx).1, hUopen, hbdd, hJ, by rw [h1]; exact hconn1,
      by rw [h2]; exact hconn2⟩
  · exact ⟨U, hUnhds, fun x hx => (hUV hx).1, hUopen, hbdd, hJ, by rw [h1]; exact hconn2,
      by rw [h2]; exact hconn1⟩

/-- The two neighbourhoods of `w` used in the construction of Fig. 8(3) of
Klein–Langetepe–Nilforoushan (2009), with *all four* connectedness statements of Theorem 4.

This is `AVD.CurveSystem.exists_crosscut_nbhds` strengthened by the connectedness of
`U ∩ D(p,q)` and of `Ur ∩ D(p,r)`, which is what the degenerate configuration in which the
two curves coincide near `w` needs. -/
theorem exists_crosscut_nbhds_both (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane} {f g : ℝ → Plane}
    (hf : IsProperLineParamAt f (C.J p q) w) (hg : IsProperLineParamAt g (C.J p r) w)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ U Ur : Set Plane, IsOpen U ∧ Bornology.IsBounded U ∧
      IsClosedJordanCurve (frontier U) ∧ IsConnected (U ∩ C.D q p) ∧
      IsConnected (U ∩ C.D p q) ∧ w ∈ U ∧
      (∀ t : ℝ, f t ∈ U → |t| < δ₀) ∧ (∀ t : ℝ, g t ∈ U → |t| < δ₀) ∧
      Ur ∈ 𝓝 w ∧ Ur ⊆ U ∧ IsOpen Ur ∧ IsConnected (Ur ∩ C.D r p) ∧
      IsConnected (Ur ∩ C.D p r) := by
  have hwq : w ∈ C.J p q := by rw [← hf.2, ← hf.1.2.2.1]; exact mem_range_self 0
  have hwr : w ∈ C.J p r := by rw [← hg.2, ← hg.1.2.2.1]; exact mem_range_self 0
  obtain ⟨Wf, hWfopen, hwWf, hWfsub⟩ := hf.1.exists_nbhd hδ₀
  obtain ⟨Wg, hWgopen, hwWg, hWgsub⟩ := hg.1.exists_nbhd hδ₀
  rw [hf.2] at hwWf
  rw [hg.2] at hwWg
  obtain ⟨U, hUnhds, hUV0, hUopen, hUbdd, hUJ, hUconn, hUconn'⟩ :=
    exists_theorem4_jordan_nbhd_both hadm hq hp (Ne.symm hpq)
      (by rw [← C.J_symm hp hq hpq]; exact hwq)
      (Filter.inter_mem (hWfopen.mem_nhds hwWf) (hWgopen.mem_nhds hwWg))
  obtain ⟨Ur, hUrnhds, hUrU, hUropen, -, -, hUrconn, hUrconn'⟩ :=
    exists_theorem4_jordan_nbhd_both hadm hr hp (Ne.symm hpr)
      (by rw [← C.J_symm hp hr hpr]; exact hwr) hUnhds
  refine ⟨U, Ur, hUopen, hUbdd, hUJ, hUconn, hUconn', mem_of_mem_nhds hUnhds, ?_, ?_,
    hUrnhds, hUrU, hUropen, hUrconn, hUrconn'⟩
  · intro t ht
    obtain ⟨s, hs, hst⟩ :=
      hWfsub ⟨by rw [← hf.1.2.2.1]; exact mem_range_self t, (hUV0 ht).1⟩
    rw [← hf.1.2.1 hst, abs_lt]
    exact ⟨hs.1, hs.2⟩
  · intro t ht
    obtain ⟨s, hs, hst⟩ :=
      hWgsub ⟨by rw [← hg.1.2.2.1]; exact mem_range_self t, (hUV0 ht).2⟩
    rw [← hg.1.2.1 hst, abs_lt]
    exact ⟨hs.1, hs.2⟩

/-- **The degenerate configuration in which the two curves coincide near `w`**: both
branches of `J(p,r)` at `w` lie on `J(p,q)`.

Then the piece `κ` of `J(p,r)` inside a Theorem 4 neighbourhood `U` of `w` lies on *both*
curves, so it avoids each of the four half-planes.  Let `Ω` be the domain that `κ` cuts off
from `U` on the side away from `D(q,p)`, and `Ω'` the other one; by the construction of
Fig. 8(3) (`AVD.CurveSystem.access_of_crosscut_aux`) it suffices to rule out that `Ω`
swallows `Ur ∩ D(r,p)`.  Assume it does.  Since `Ω ⊆ D(p,q)` and `U ∩ D(p,q)` is connected
and avoids `κ`, the whole of `U ∩ D(p,q)` lies in `Ω`.  The connected set `Ur ∩ D(p,r)` also
avoids `κ`, so it lies in `Ω` or in `Ω'`:

* if it lies in `Ω'`, then a point of the Voronoi region of `p` near `w` — there is one,
  because `w` lies on the frontier of that region — would lie in `Ω ∩ Ω' = ∅`;
* if it lies in `Ω`, then all of `Ur ∖ J(p,r)` lies in `Ω`, so the non-empty open set
  `Ω' ∩ Ur` is contained in the curve `J(p,r)`, which is the frontier of `D(p,r)` and hence
  contains no open set.

Both cases are impossible, so `w` is accessible from `VR(p,{p,q,r})`.  Note that this is
the only place where the hypothesis `w ∈ frontier (VR p)` is used in the proof of Lemma 8
other than through Lemma 7. -/
theorem shared_both_branches_access (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane}
    (hwq : w ∈ C.J p q) (hw : w ∈ frontier (C.VR p {p, q, r}))
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hGb : BranchBefore g (C.J p q)) (hGa : BranchAfter g (C.J p q)) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  obtain ⟨δ1, hδ1, hsub1⟩ := hGb
  obtain ⟨δ2, hδ2, hsub2⟩ := hGa
  have hmin : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  set δ₀ : ℝ := min δ1 δ2 / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  have hb1 : δ₀ < δ1 := by have h := min_le_left δ1 δ2; rw [hδ₀def]; linarith
  have hb2 : δ₀ < δ2 := by have h := min_le_right δ1 δ2; rw [hδ₀def]; linarith
  obtain ⟨U, Ur, hUopen, hUbdd, hUJ, hUconn, hUconn', hwU, -, hboundg, hUrnhds, hUrU,
    hUropen, hUrconn, hUrconn'⟩ :=
    exists_crosscut_nbhds_both hadm hp hq hr hpq hpr hf hg hδ₀
  obtain ⟨a, ha, hgU, hga⟩ :=
    hg.1.exists_first_exit_neg hUopen hUbdd (by rw [hg.2]; exact hwU)
  obtain ⟨c, hc, hgU', hgc⟩ :=
    hg.1.exists_first_exit hUopen hUbdd (by rw [hg.2]; exact hwU)
  have hage : -δ₀ ≤ a := by
    by_contra hcon
    push Not at hcon
    have h := hboundg _ (hgU ⟨-δ₀, ⟨hcon, by linarith⟩, rfl⟩)
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  have hcle : c ≤ δ₀ := by
    by_contra hcon
    push Not at hcon
    have h := hboundg _ (hgU' ⟨δ₀, ⟨hδ₀.le, hcon⟩, rfl⟩)
    rw [abs_of_nonneg hδ₀.le] at h
    linarith
  have hac : a < c := lt_trans ha hc
  have hκIoo : subarcParam g a c '' Ioo 0 1 = g '' Ioo a c := subarcParam_image_Ioo hac
  have hκIcc : subarcParam g a c '' Icc 0 1 = g '' Icc a c := subarcParam_image hac.le
  have hIooU : g '' Ioo a c ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    rcases le_or_gt t 0 with h | h
    · exact hgU ⟨t, ⟨ht.1, h⟩, rfl⟩
    · exact hgU' ⟨t, ⟨h.le, ht.2⟩, rfl⟩
  -- the crosscut lies on both curves
  have hκJq : ∀ x ∈ subarcParam g a c '' Icc 0 1, x ∈ C.J p q := by
    intro x hx
    rw [hκIcc] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    rcases lt_trichotomy t 0 with h | h | h
    · exact hsub1 ⟨t, ⟨lt_of_lt_of_le (by linarith) ht.1, h⟩, rfl⟩
    · rw [h, hg.2]; exact hwq
    · exact hsub2 ⟨t, ⟨h, lt_of_le_of_lt ht.2 (by linarith)⟩, rfl⟩
  have hκJr : ∀ x ∈ subarcParam g a c '' Icc 0 1, x ∈ C.J p r := by
    intro x hx
    rw [hκIcc] at hx
    obtain ⟨t, -, rfl⟩ := hx
    rw [← hg.1.2.2.1]; exact mem_range_self t
  have hwκ : w ∈ subarcParam g a c '' Ioo 0 1 := by
    rw [hκIoo]; exact ⟨0, ⟨ha, hc⟩, hg.2⟩
  refine access_of_crosscut_aux hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds
    hUrU hUropen hUrconn (isArc_subarcParam hg.1.1 hg.1.2.1 hac)
    (by rw [subarcParam_zero]; exact hga) (by rw [subarcParam_one]; exact hgc) ?_
    (by rw [hκIoo]; exact hIooU) hwκ
    (fun x hx => (notMem_D_of_mem_J hp hq hpq (hκJq x hx)).2)
    (fun x hx => (notMem_D_of_mem_J hp hr hpr (hκJr x hx)).2) ?_
  · rw [subarcParam_zero, subarcParam_one]
    intro hcon
    have : a = c := hg.1.2.1 hcon
    linarith
  rintro Ω Ω' hΩo hΩ'o hdisjΩ hΩU hΩ'U hΩne hκΩ' hcover hΩpq hqpΩ' h
  -- the half-plane `D(p,q)` lies in `Ω`
  have hpqΩ : U ∩ C.D p q ⊆ Ω := by
    have hcov : U ∩ C.D p q ⊆ Ω ∪ Ω' := fun x hx =>
      hcover x hx.1 (fun hxκ => (notMem_D_of_mem_J hp hq hpq (hκJq x hxκ)).1 hx.2)
    rcases hUconn'.isPreconnected.subset_or_subset hΩo hΩ'o hdisjΩ hcov with h' | h'
    · exact h'
    · exfalso
      obtain ⟨x, hx⟩ := hΩne
      exact (Set.disjoint_left.1 hdisjΩ) hx (h' ⟨hΩU hx, hΩpq hx⟩)
  -- and the half-plane `D(p,r)` lies in one of the two domains
  have hcovr : Ur ∩ C.D p r ⊆ Ω ∪ Ω' := fun x hx =>
    hcover x (hUrU hx.1)
      (fun hxκ => (notMem_D_of_mem_J hp hr hpr (hκJr x hxκ)).1 hx.2)
  rcases hUrconn'.isPreconnected.subset_or_subset hΩo hΩ'o hdisjΩ hcovr with h' | h'
  · -- then `Ω' ∩ Ur` is a non-empty open subset of the curve `J(p,r)`
    have hwfr : w ∈ frontier Ω' := hκΩ' (Set.image_mono Ioo_subset_Icc_self hwκ)
    obtain ⟨y, hyUr, hyΩ'⟩ :=
      mem_closure_iff.1 hwfr.1 Ur hUropen (mem_of_mem_nhds hUrnhds)
    have hsubJ : ∀ x ∈ Ω' ∩ Ur, x ∈ C.J p r := by
      intro x hx
      by_contra hxJ
      have hx' : x ∈ (C.J p r)ᶜ := hxJ
      rw [C.compl_J p hp r hr hpr] at hx'
      rcases hx' with hx' | hx'
      · exact (Set.disjoint_left.1 hdisjΩ) (h' ⟨hx.2, hx'⟩) hx.1
      · exact (Set.disjoint_left.1 hdisjΩ) (h ⟨hx.2, hx'⟩) hx.1
    have hyclos : y ∈ closure (C.D p r) :=
      mem_closure_D_of_mem_J hadm hp hr hpr (hsubJ y ⟨hyΩ', hyUr⟩)
    obtain ⟨z, hz1, hz2⟩ :=
      mem_closure_iff.1 hyclos (Ω' ∩ Ur) (hΩ'o.inter hUropen) ⟨hyΩ', hyUr⟩
    exact (notMem_D_of_mem_J hp hr hpr (hsubJ z hz1)).1 hz2
  · -- then the Voronoi region of `p` is empty near `w`
    obtain ⟨v, hvUr, hvVR⟩ :=
      mem_closure_iff.1 (frontier_subset_closure hw) Ur hUropen (mem_of_mem_nhds hUrnhds)
    rw [VR_triple rfl hpq hpr] at hvVR
    exact (Set.disjoint_left.1 hdisjΩ) (hpqΩ ⟨hUrU hvUr, hvVR.1⟩) (h' ⟨hvUr, hvVR.2⟩)

/-- **The construction of Fig. 8(3)** of Klein–Langetepe–Nilforoushan (2009) in the
degenerate configurations, where the joining set is a common point of the two curves.

The hypotheses on the two branches are those of configuration BC — the branch `F⁻` of
`J(p,q)` lies in the closure of `D(p,r)`, the branch `G⁺` of `J(p,r)` lies in the closure of
`D(p,q)`, and `G⁺` is not contained in `J(p,q)` — so that
`AVD.CurveSystem.exists_branch_disjoint` and `AVD.CurveSystem.exists_crosscut_arc` build the
crosscut `κ` out of `F⁻` and `G⁺` exactly as in `AVD.CurveSystem.bc_configuration_access`.
What replaces the hypothesis that the fourth quadrant at `w` is non-empty is the existence,
arbitrarily close to `w`, of common points of the two curves lying neither on `F⁻` nor on
`G⁺`; such a point is a joining set (`AVD.CurveSystem.access_of_crosscut_common_point`). -/
theorem shared_crosscut_access (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hFb : BranchBefore f (closure (C.D p r)))
    (hGa : BranchAfter g (closure (C.D p q)))
    (hndG : ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, g x ∉ C.J p q)
    (hjoinpt : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.J p q ∧ z ∈ C.J p r ∧
      z ∉ f '' Iic 0 ∧ z ∉ g '' Ici 0) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hwq : w ∈ C.J p q := by rw [← hf.2, ← hf.1.2.2.1]; exact mem_range_self 0
  have hwr : w ∈ C.J p r := by rw [← hg.2, ← hg.1.2.2.1]; exact mem_range_self 0
  obtain ⟨δ', hδ', δ'', hδ'', hdisjbr⟩ :=
    exists_branch_disjoint hadm hp hq hr hpq hqr hpr hf hg hFb hGa hndG
  obtain ⟨δF, hδF, hFsub⟩ := hFb
  obtain ⟨δG, hδG, hGsub⟩ := hGa
  have hmin1 : 0 < min δ' δ'' := lt_min hδ' hδ''
  have hmin2 : 0 < min δF δG := lt_min hδF hδG
  set δ₀ : ℝ := min (min δ' δ'') (min δF δG) / 2 with hδ₀def
  have hminpos : 0 < min (min δ' δ'') (min δF δG) := lt_min hmin1 hmin2
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  have hb1 : δ₀ < δ' := by
    have h := (min_le_left (min δ' δ'') (min δF δG)).trans (min_le_left δ' δ'')
    rw [hδ₀def]; linarith
  have hb2 : δ₀ < δ'' := by
    have h := (min_le_left (min δ' δ'') (min δF δG)).trans (min_le_right δ' δ'')
    rw [hδ₀def]; linarith
  have hb3 : δ₀ < δF := by
    have h := (min_le_right (min δ' δ'') (min δF δG)).trans (min_le_left δF δG)
    rw [hδ₀def]; linarith
  have hb4 : δ₀ < δG := by
    have h := (min_le_right (min δ' δ'') (min δF δG)).trans (min_le_right δF δG)
    rw [hδ₀def]; linarith
  obtain ⟨U, Ur, hUopen, hUbdd, hUJ, hUconn, hwU, hboundf, hboundg, hUrnhds, hUrU, hUropen,
    hUrconn⟩ := exists_crosscut_nbhds hadm hp hq hr hpq hpr hf hg hδ₀
  obtain ⟨a, ha, hfU, hfa⟩ :=
    hf.1.exists_first_exit_neg hUopen hUbdd (by rw [hf.2]; exact hwU)
  obtain ⟨b, hb, hgU, hgb⟩ :=
    hg.1.exists_first_exit hUopen hUbdd (by rw [hg.2]; exact hwU)
  have hage : -δ₀ ≤ a := by
    by_contra hcon
    push Not at hcon
    have h := hboundf _ (hfU ⟨-δ₀, ⟨hcon, by linarith⟩, rfl⟩)
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  have hble : b ≤ δ₀ := by
    by_contra hcon
    push Not at hcon
    have h := hboundg _ (hgU ⟨δ₀, ⟨hδ₀.le, hcon⟩, rfl⟩)
    rw [abs_of_nonneg hδ₀.le] at h
    linarith
  -- the two pieces of the crosscut meet only at `w`
  have hmeet : f '' Icc a 0 ∩ g '' Icc 0 b ⊆ {w} := by
    rintro x ⟨⟨s, hs, rfl⟩, ⟨t, ht, hst⟩⟩
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h, hf.2]; rfl
    rcases eq_or_lt_of_le ht.1 with h' | h'
    · rw [← hst, ← h', hg.2]; rfl
    exfalso
    refine (Set.disjoint_left.1 hdisjbr) (a := g t)
      ⟨t, ⟨h', lt_of_le_of_lt ht.2 (lt_of_le_of_lt hble hb1)⟩, rfl⟩ ?_
    exact ⟨s, ⟨lt_of_lt_of_le (by linarith) hs.1, h⟩, hst.symm⟩
  have hfane : f a ≠ g b := by
    intro hcon
    have hmem : f a ∈ ({w} : Set Plane) :=
      hmeet ⟨⟨a, ⟨le_refl a, ha.le⟩, rfl⟩, ⟨b, ⟨hb.le, le_refl b⟩, hcon.symm⟩⟩
    have : a = 0 := hf.1.2.1 (by rw [hmem, hf.2])
    linarith
  obtain ⟨κ, hκarc, hκ0, hκ1, hκimg, hκint, hwκ⟩ :=
    exists_crosscut_arc hf.1.1 hf.1.2.1 hg.1.1 hg.1.2.1 hf.2 hg.2 ha hb hfU hgU hmeet
  have hκq : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D q p := by
    intro x hx
    rw [hκimg] at hx
    rcases hx with ⟨s, -, rfl⟩ | ⟨t, ht, rfl⟩
    · intro hc
      have : f s ∈ (C.J p q)ᶜ := by rw [C.compl_J p hp q hq hpq]; exact Or.inr hc
      exact this (by rw [← hf.1.2.2.1]; exact mem_range_self s)
    · refine notMem_D_of_mem_closure hadm hp hq hpq ?_
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hg.2]; exact mem_closure_D_of_mem_J hadm hp hq hpq hwq
      · exact hGsub ⟨t, ⟨h, lt_of_le_of_lt ht.2 (lt_of_le_of_lt hble hb4)⟩, rfl⟩
  have hκr : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D r p := by
    intro x hx
    rw [hκimg] at hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨t, -, rfl⟩
    · refine notMem_D_of_mem_closure hadm hp hr hpr ?_
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h, hf.2]; exact mem_closure_D_of_mem_J hadm hp hr hpr hwr
      · exact hFsub ⟨s, ⟨lt_of_lt_of_le (by linarith) hs.1, h⟩, rfl⟩
    · intro hc
      have : g t ∈ (C.J p r)ᶜ := by rw [C.compl_J p hp r hr hpr]; exact Or.inr hc
      exact this (by rw [← hg.1.2.2.1]; exact mem_range_self t)
  obtain ⟨z, hzUr, hzq, hzr, hzf, hzg⟩ := hjoinpt Ur hUrnhds
  have hzκ : z ∉ κ '' Icc 0 1 := by
    rw [hκimg]
    rintro (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact hzf ⟨s, hs.2, rfl⟩
    · exact hzg ⟨t, ht.1, rfl⟩
  exact access_of_crosscut_common_point hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU
    hUrnhds hUrU hUropen hUrconn hκarc (by rw [hκ0]; exact hfa) (by rw [hκ1]; exact hgb)
    (by rw [hκ0, hκ1]; exact hfane) hκint hwκ hκq hκr hzUr hzκ hzq hzr

/-- **The degenerate configurations of the proof of Lemma 8** of
Klein–Langetepe–Nilforoushan (2009), in the normalised form in which the branch `G⁺` of
`J(p,r)` after `w` is contained in `J(p,q)` — the two curves share a segment at `w` — and in
which, as in configuration AA of Fig. 7, each branch of one curve lies in the closure of the
half-plane of the other curve labelled by `p`.

If the branch `G⁻` is shared as well, the two curves coincide near `w` and
`AVD.CurveSystem.shared_both_branches_access` applies.  Otherwise the crosscut of Fig. 8(3)
is built from `G⁻` and from one of the two branches of `J(p,q)`, and the shared branch `G⁺`
provides the common point of the two curves off the crosscut which
`AVD.CurveSystem.shared_crosscut_access` needs: the points of `G⁺` near `w` lie on `J(p,q)`,
hence on one of its two branches, and it is the *other* one that is used for the crosscut.
-/
theorem shared_branch_access (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    (hwq : w ∈ C.J p q) (hw : w ∈ frontier (C.VR p {p, q, r}))
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hFb : BranchBefore f (closure (C.D p r))) (hFa : BranchAfter f (closure (C.D p r)))
    (hGb : BranchBefore g (closure (C.D p q)))
    (hGshared : BranchAfter g (C.J p q)) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  by_cases hGb' : BranchBefore g (C.J p q)
  · exact shared_both_branches_access hadm hp hq hr hpq hpr hwq hw hf hg hGb' hGshared
  obtain ⟨δ, hδ, hδsub⟩ := hGshared
  have hg' : IsProperLineParamAt (fun t => g (-t)) (C.J p r) w := hg.rev
  have hG'a : BranchAfter (fun t => g (-t)) (closure (C.D p q)) := hGb.rev
  have hnd' : ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, (fun t => g (-t)) x ∉ C.J p q :=
    exists_notMem_of_not_branchBefore hGb'
  -- the shared branch accumulates at `w`
  have hpts : ∀ V ∈ 𝓝 w, ∃ t ∈ Ioo (0 : ℝ) δ, g t ∈ V := by
    intro V hV
    have hpre : g ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      hg.1.1.continuousAt.preimage_mem_nhds (by rw [hg.2]; exact hV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
    have hm : 0 < min ε δ := lt_min hε hδ
    refine ⟨min ε δ / 2, ⟨by linarith, by have := min_le_right ε δ; linarith⟩, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    have := min_le_left ε δ
    linarith
  -- the points of the shared branch never lie on the branch `G⁻`
  have hnotG : ∀ t ∈ Ioo (0 : ℝ) δ, g t ∉ (fun u => g (-u)) '' Ici 0 := by
    rintro t ht ⟨s, hs, hst⟩
    simp only [mem_Ici] at hs
    have : t = -s := hg.1.2.1 hst.symm
    linarith [ht.1]
  by_cases hcase : ∀ V ∈ 𝓝 w, ∃ t ∈ Ioo (0 : ℝ) δ, g t ∈ V ∧ g t ∉ f '' Iic 0
  · refine shared_crosscut_access hadm hp hq hr hpq hqr hpr hf hg' hFb hG'a hnd' ?_
    intro V hV
    obtain ⟨t, ht, htV, htf⟩ := hcase V hV
    exact ⟨g t, htV, hδsub ⟨t, ht, rfl⟩, by rw [← hg.1.2.2.1]; exact mem_range_self t,
      htf, hnotG t ht⟩
  · push Not at hcase
    obtain ⟨V₀, hV₀, hV₀sub⟩ := hcase
    refine shared_crosscut_access hadm hp hq hr hpq hqr hpr hf.rev hg' hFa.rev hG'a hnd' ?_
    intro V hV
    obtain ⟨t, ht, htV⟩ := hpts (V ∩ V₀) (Filter.inter_mem hV hV₀)
    obtain ⟨s, hs, hst⟩ := hV₀sub t ht htV.2
    have hsne : s ≠ 0 := by
      rintro rfl
      rw [hf.2] at hst
      have : t = 0 := hg.1.2.1 (by rw [hg.2, hst])
      linarith [ht.1]
    simp only [mem_Iic] at hs
    have hsneg : s < 0 := lt_of_le_of_ne hs hsne
    refine ⟨g t, htV.1, hδsub ⟨t, ht, rfl⟩, by rw [← hg.1.2.2.1]; exact mem_range_self t,
      ?_, hnotG t ht⟩
    rw [image_Iic_rev]
    rintro ⟨u, hu, hut⟩
    simp only [mem_Ici] at hu
    have : s = u := hf.1.2.1 (by rw [hst, hut])
    linarith

end CurveSystem

end AVD
