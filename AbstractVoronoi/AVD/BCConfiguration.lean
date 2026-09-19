import AbstractVoronoi.AVD.CrossingCases
import AbstractVoronoi.Jordan.CrosscutSplit
import AbstractVoronoi.Paper.Theorem4

/-!
# Configuration BC of Fig. 7 in the proof of Lemma 8

This file carries out the construction of Fig. 8(3) of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

which settles configuration **BC** in the proof of **Lemma 8**, the case the paper calls
"the most interesting one": the two bisecting curves `J(p,q)` and `J(p,r)` cross at the
boundary point `w` of `VR(p,{p,q,r})`, and an arc accessing `w` from inside `VR(p,{p,q,r})`
has to be produced.

The main result is `AVD.CurveSystem.bc_configuration_access`.  The pieces it uses are

* `AVD.CurveSystem.exists_branch_disjoint` — a subsegment of `G⁺` with endpoint `w` is
  disjoint from `F⁻` (the separation step of the paper, proved in
  `AbstractVoronoi.AVD.CrossingCases`);
* `AVD.CurveSystem.exists_crosscut_arc` — those two subsegments form a crosscut `κ` of a
  Theorem 4 neighbourhood `U` of `w`;
* `AVD.exists_crosscut_split` — the crosscut cuts `U` into two Jordan domains;
* Theorem 4 itself, in the two forms `AVD.CurveSystem.exists_theorem4_jordan_nbhd` (for the
  neighbourhood `U`, whose frontier must be a closed Jordan curve) and
  `AVD.accessibleFrom_of_jordan_domain` (accessibility of `w` from the domain cut off by the
  crosscut).

The step that the paper leaves to Fig. 8(3) — the identification of the domain `D` cut off
by the crosscut as a part of the Voronoi region of `p` — is carried out here without any
orientation convention: of the two domains cut out by `κ`, the one which does *not* contain
the connected set `U ∩ D(q,p)` is shown to avoid both `D(q,p)` and, near `w`, `D(r,p)`,
hence to be contained in `D(p,q) ∩ D(p,r) = VR(p,{p,q,r})`.
-/

noncomputable section

open Set Topology

namespace AVD

/-- **Accessibility of a boundary point of a Jordan domain, inside a prescribed
neighbourhood.**

If `Ω` is a non-empty bounded domain whose frontier is a closed Jordan curve, then every
point `w` of that frontier is accessible from `Ω` by an arc contained in any prescribed
neighbourhood `V` of `w`.

This is the local part of **Theorem 4** of Klein–Langetepe–Nilforoushan (2009)
(`AVD.jordanCurveLocalAccessibility`), combined with the identification of `Ω` as a
complementary domain of its own frontier (`AVD.exists_exterior_of_frontier_jordan`).  It is
the last step of the proof of Lemma 8 in configuration BC:

> Theorem 4 provides an arc `α` with endpoint `w` such that `α ∖ {w}` is contained in `D`. -/
theorem accessibleFrom_of_jordan_domain {Ω V : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (hbdd : Bornology.IsBounded Ω) (hJ : IsClosedJordanCurve (frontier Ω))
    {w : Plane} (hw : w ∈ frontier Ω) (hV : V ∈ 𝓝 w) :
    AccessibleFrom (Ω ∩ V) w := by
  obtain ⟨E, hEo, hΩc, hEc, hΩE, hunion, hfE⟩ :=
    exists_exterior_of_frontier_jordan hΩ hne hbdd hJ
  obtain ⟨U, -, hUV, -, -, hc1, -, hacc1, -⟩ :=
    jordanCurveLocalAccessibility (frontier Ω) (Or.inl hJ) Ω E hΩ hEo hΩc hEc hΩE hunion rfl
      hfE w hw V hV
  obtain ⟨x, hx⟩ := hc1.nonempty
  obtain ⟨α, harc, -, h1, hsub⟩ := hacc1 x hx
  exact ⟨α, harc, h1, fun y hy => ⟨(hsub hy).2, hUV (hsub hy).1⟩⟩

/-! ## Reversing the orientation of a parametrization -/

/-- Reversing the parameter of a proper parametrization of a curve through `w` gives again a
proper parametrization of the same curve through `w`.  This is what allows the four
configurations of Fig. 7 of Klein–Langetepe–Nilforoushan (2009) to be treated with one
fixed choice of the branches, namely `F⁻` and `G⁺`. -/
theorem IsProperLineParamAt.rev {γ : ℝ → Plane} {Cu : Set Plane} {w : Plane}
    (h : IsProperLineParamAt γ Cu w) : IsProperLineParamAt (fun t => γ (-t)) Cu w := by
  obtain ⟨⟨hc, hi, hr, hpr⟩, h0⟩ := h
  refine ⟨⟨hc.comp continuous_neg, ?_, ?_, ?_⟩, by simpa using h0⟩
  · intro a b hab
    have := hi hab
    linarith
  · apply Subset.antisymm
    · rintro x ⟨t, rfl⟩
      rw [← hr]
      exact ⟨-t, rfl⟩
    · intro x hx
      rw [← hr] at hx
      obtain ⟨t, rfl⟩ := hx
      exact ⟨-t, by simp⟩
  · intro K hK
    exact (Homeomorph.isCompact_preimage (Homeomorph.neg ℝ)).2 (hpr K hK)

/-- Under the reversal of the parameter, the branch before the base point becomes the branch
after it. -/
theorem BranchBefore.rev {γ : ℝ → Plane} {A : Set Plane} (h : BranchBefore γ A) :
    BranchAfter (fun t => γ (-t)) A := by
  obtain ⟨δ, hδ, hsub⟩ := h
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hsub ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩

/-- Under the reversal of the parameter, the branch after the base point becomes the branch
before it. -/
theorem BranchAfter.rev {γ : ℝ → Plane} {A : Set Plane} (h : BranchAfter γ A) :
    BranchBefore (fun t => γ (-t)) A := by
  obtain ⟨δ, hδ, hsub⟩ := h
  refine ⟨δ, hδ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hsub ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩

/-- A branch which is *not* contained in a set meets its complement arbitrarily close to the
base point.  This is the form in which the non-degeneracy assumption of footnote 8 of
Klein–Langetepe–Nilforoushan (2009) — no branch of one curve is contained in the other
curve — is used. -/
theorem exists_notMem_of_not_branchAfter {γ : ℝ → Plane} {A : Set Plane}
    (h : ¬ BranchAfter γ A) : ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, γ x ∉ A := by
  intro ε hε
  by_contra hc
  push Not at hc
  exact h ⟨ε, hε, by rintro _ ⟨x, hx, rfl⟩; exact hc x hx⟩

/-- The version of `AVD.exists_notMem_of_not_branchAfter` for the branch before the base
point, stated for the reversed parametrization. -/
theorem exists_notMem_of_not_branchBefore {γ : ℝ → Plane} {A : Set Plane}
    (h : ¬ BranchBefore γ A) :
    ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, (fun t => γ (-t)) x ∉ A := by
  intro ε hε
  by_contra hc
  push Not at hc
  refine h ⟨ε, hε, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hc (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa using this

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- A point in the closure of the half-plane `D(p,q)` does not lie in the opposite
half-plane `D(q,p)`; a consequence of Theorem 4 of Klein–Langetepe–Nilforoushan (2009),
through `AVD.CurveSystem.closure_D_eq`. -/
theorem notMem_D_of_mem_closure (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {x : Plane} (hx : x ∈ closure (C.D p q)) : x ∉ C.D q p := by
  intro hx'
  rw [closure_D_eq hadm hp hq hpq] at hx
  rcases hx with h | h
  · exact (Set.disjoint_left.1 (C.D_disjoint p hp q hq hpq)) h hx'
  · have : x ∈ (C.J p q)ᶜ := by rw [C.compl_J p hp q hq hpq]; exact Or.inr hx'
    exact this h

/-- **Theorem 4** of Klein–Langetepe–Nilforoushan (2009) for a bisecting curve `J(p,q)`, in
the strengthened form needed for the construction of Fig. 8(3): the neighbourhood `U` of a
point `z` of the curve can be taken *bounded* and with a *closed Jordan curve* as frontier,
in addition to meeting the half-plane `D(p,q)` in a connected set.

The two extra pieces of data are part of the statement of Theorem 4 ("there exists a
neighbourhood `U` whose boundary is homeomorphic to a circle") but are dropped by
`AVD.CurveSystem.exists_theorem4_data`, which is all that the earlier proofs need.  They are
what makes the crosscut theorem `AVD.exists_crosscut_split` applicable to `U`. -/
theorem exists_theorem4_jordan_nbhd (hadm : C.Admissible) {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane} (hz : z ∈ C.J p q)
    {V : Set Plane} (hV : V ∈ 𝓝 z) :
    ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧ Bornology.IsBounded U ∧
      IsClosedJordanCurve (frontier U) ∧ IsConnected (U ∩ C.D p q) := by
  obtain ⟨D₁, D₂, hO1, hO2, hc1, hc2, hd12, hu12, hf1, hf2⟩ :=
    (hadm.A1 p hp q hq hpq).exists_separation_frontier_eq
  have hacc := jordanCurveLocalAccessibility (C.J p q) (Or.inr (hadm.A1 p hp q hq hpq))
    D₁ D₂ hO1 hO2 hc1 hc2 hd12 hu12 hf1 hf2
  have hV' : V ∩ Metric.ball z 1 ∈ 𝓝 z :=
    Filter.inter_mem hV (Metric.ball_mem_nhds z one_pos)
  rcases D_eq_of_separation hadm hp hq hpq hc1 hc2 hu12 with hkey | hkey
  · obtain ⟨U, hUnhds, hUV, hUopen, hJ, hconn, -, -, -⟩ := hacc z hz _ hV'
    exact ⟨U, hUnhds, fun x hx => (hUV hx).1, hUopen,
      Metric.isBounded_ball.subset fun x hx => (hUV hx).2, hJ, by rw [hkey]; exact hconn⟩
  · obtain ⟨U, hUnhds, hUV, hUopen, hJ, -, hconn, -, -⟩ := hacc z hz _ hV'
    exact ⟨U, hUnhds, fun x hx => (hUV hx).1, hUopen,
      Metric.isBounded_ball.subset fun x hx => (hUV hx).2, hJ, by rw [hkey]; exact hconn⟩

/-- The two neighbourhoods of `w` used in the construction of Fig. 8(3) of
Klein–Langetepe–Nilforoushan (2009): a Theorem 4 neighbourhood `U` of `w` for the curve
`J(p,q)`, bounded, with a closed Jordan curve as frontier and meeting `D(q,p)` in a
connected set, and, inside it, a Theorem 4 neighbourhood `Ur` of `w` for the curve `J(p,r)`
meeting `D(r,p)` in a connected set.

The neighbourhood `U` is moreover taken small enough that the two curves meet it only in
their branches at `w`: a point `f t` or `g t` of `U` has `|t| < δ₀`, for a prescribed
`δ₀ > 0`.  This uses that a proper parametrization is a closed embedding
(`AVD.IsProperLineParam.exists_nbhd`) and is what keeps the first exit points of the two
curves from `U` inside the ranges in which the branch hypotheses apply. -/
theorem exists_crosscut_nbhds (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane} {f g : ℝ → Plane}
    (hf : IsProperLineParamAt f (C.J p q) w) (hg : IsProperLineParamAt g (C.J p r) w)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ U Ur : Set Plane, IsOpen U ∧ Bornology.IsBounded U ∧
      IsClosedJordanCurve (frontier U) ∧ IsConnected (U ∩ C.D q p) ∧ w ∈ U ∧
      (∀ t : ℝ, f t ∈ U → |t| < δ₀) ∧ (∀ t : ℝ, g t ∈ U → |t| < δ₀) ∧
      Ur ∈ 𝓝 w ∧ Ur ⊆ U ∧ IsOpen Ur ∧ IsConnected (Ur ∩ C.D r p) := by
  have hwq : w ∈ C.J p q := by rw [← hf.2, ← hf.1.2.2.1]; exact mem_range_self 0
  have hwr : w ∈ C.J p r := by rw [← hg.2, ← hg.1.2.2.1]; exact mem_range_self 0
  obtain ⟨Wf, hWfopen, hwWf, hWfsub⟩ := hf.1.exists_nbhd hδ₀
  obtain ⟨Wg, hWgopen, hwWg, hWgsub⟩ := hg.1.exists_nbhd hδ₀
  rw [hf.2] at hwWf
  rw [hg.2] at hwWg
  obtain ⟨U, hUnhds, hUV0, hUopen, hUbdd, hUJ, hUconn⟩ :=
    exists_theorem4_jordan_nbhd hadm hq hp (Ne.symm hpq)
      (by rw [← C.J_symm hp hq hpq]; exact hwq)
      (Filter.inter_mem (hWfopen.mem_nhds hwWf) (hWgopen.mem_nhds hwWg))
  obtain ⟨-, haccr⟩ := exists_theorem4_data hadm hr hp (Ne.symm hpr)
  obtain ⟨Ur, hUrnhds, hUrU, hUropen, hUrconn, -⟩ :=
    haccr w (by rw [← C.J_symm hp hr hpr]; exact hwr) U hUnhds
  refine ⟨U, Ur, hUopen, hUbdd, hUJ, hUconn, mem_of_mem_nhds hUnhds, ?_, ?_, hUrnhds, hUrU,
    hUropen, hUrconn⟩
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

/-- **The identification of the domain `D` of Fig. 8(3)** in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009), and the access arc it provides.

Let `U` be a Theorem 4 neighbourhood of `w` for the curve `J(p,q)` — bounded, with a closed
Jordan curve as frontier, and meeting the half-plane `D(q,p)` in a connected set — let `Ur`
be a Theorem 4 neighbourhood of `w` for the curve `J(p,r)` inside `U`, meeting `D(r,p)` in a
connected set, and let `κ` be a crosscut of `U` through `w` which meets neither `D(q,p)` nor
`D(r,p)`.  Assume finally that points of `D(q,p) ∩ D(r,p)` occur arbitrarily close to `w`.
Then `w` is accessible from `VR(p,{p,q,r})`.

This is the heart of the argument, and it replaces the appeal of the paper to Fig. 8(3) by a
proof that uses no orientation convention.  The crosscut cuts `U` into two domains
(`AVD.exists_crosscut_split`); let `Ω` be the one which does *not* contain the connected set
`U ∩ D(q,p)`.  Then

* `Ω` misses `D(q,p)`, and, being open, it misses the curve `J(p,q)` as well — a point of
  `J(p,q)` in `Ω` would have a whole disc of `Ω` around it, and that disc meets `D(q,p)`,
  of which `J(p,q)` is the frontier.  So `Ω ⊆ D(p,q)`.
* Inside `Ur`, the domain `Ω` misses `D(r,p)`: otherwise the connected set `Ur ∩ D(r,p)`,
  which avoids `κ`, would be contained in `Ω`, and so would the points of
  `D(q,p) ∩ D(r,p)` near `w`, contradicting the previous item.  As before, `Ω ∩ Ur` then
  misses `J(p,r)` too, so `Ω ∩ Ur ⊆ D(p,r)`.

Hence `Ω ∩ Ur ⊆ D(p,q) ∩ D(p,r) = VR(p,{p,q,r})`, and since `w` lies on the frontier of `Ω`,
which is a closed Jordan curve, Theorem 4 applied to that curve produces an arc accessing
`w` from inside `Ω ∩ Ur` (`AVD.accessibleFrom_of_jordan_domain`).

The hypothesis that makes the second item work is stated here in the weakest form in which
it is used: the domain `Ω` cut off by the crosscut on the side away from `D(q,p)` does not
swallow the whole of `Ur ∩ D(r,p)`.  The ways of guaranteeing this are
`AVD.CurveSystem.access_of_crosscut_join` (a joining set, i.e. a preconnected subset of `Ur`
off the crosscut meeting both `D(q,p)` and `D(r,p)`, which the crosscut cannot split) and,
in the degenerate configuration in which the two curves coincide near `w`,
`AVD.CurveSystem.shared_both_branches_access`. -/
theorem access_of_crosscut_aux (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane}
    {U Ur : Set Plane} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUJ : IsClosedJordanCurve (frontier U)) (hUconn : IsConnected (U ∩ C.D q p))
    (hwU : w ∈ U) (hUrnhds : Ur ∈ 𝓝 w) (hUrU : Ur ⊆ U) (hUropen : IsOpen Ur)
    (hUrconn : IsConnected (Ur ∩ C.D r p))
    {κ : ℝ → Plane} (hκarc : IsArc κ) (hκ0 : κ 0 ∈ frontier U) (hκ1 : κ 1 ∈ frontier U)
    (hκne : κ 0 ≠ κ 1) (hκint : κ '' Ioo 0 1 ⊆ U) (hwκ : w ∈ κ '' Ioo 0 1)
    (hκq : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D q p) (hκr : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D r p)
    (hnot : ∀ Ω Ω' : Set Plane, IsOpen Ω → IsOpen Ω' → Disjoint Ω Ω' → Ω ⊆ U → Ω' ⊆ U →
      Ω.Nonempty → κ '' Icc 0 1 ⊆ frontier Ω' →
      (∀ x ∈ U, x ∉ κ '' Icc 0 1 → x ∈ Ω ∪ Ω') → Ω ⊆ C.D p q → U ∩ C.D q p ⊆ Ω' →
      ¬ (Ur ∩ C.D r p ⊆ Ω)) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hfrqp : frontier (C.D q p) = C.J p q := by
    rw [frontier_D_eq_J hadm hq hp (Ne.symm hpq), ← C.J_symm hp hq hpq]
  have hfrrp : frontier (C.D r p) = C.J p r := by
    rw [frontier_D_eq_J hadm hr hp (Ne.symm hpr), ← C.J_symm hp hr hpr]
  obtain ⟨Ω₁, Ω₂, hΩ1o, hΩ2o, hΩ1c, hΩ2c, hΩdisj, hΩ1U, hΩ2U, hJ1, hJ2, hκ1fr, hκ2fr,
    hexh⟩ :=
    exists_crosscut_split hUopen ⟨w, hwU⟩ hUbdd hUJ hκarc hκ0 hκ1 hκne hκint
  have hUqp_sub : U ∩ C.D q p ⊆ Ω₁ ∪ Ω₂ := fun x hx =>
    hexh ⟨hx.1, fun hc => hκq x hc hx.2⟩
  have hUqp := hUconn.isPreconnected.subset_or_subset hΩ1o hΩ2o hΩdisj hUqp_sub
  have hUr_sub : Ur ∩ C.D r p ⊆ Ω₁ ∪ Ω₂ := fun x hx =>
    hexh ⟨hUrU hx.1, fun hc => hκr x hc hx.2⟩
  -- the domain of Fig. 8(3) is the one *not* containing `U ∩ D(q,p)`
  have key : ∀ Ω Ω' : Set Plane, IsOpen Ω → IsOpen Ω' → Disjoint Ω Ω' → Ω ⊆ U →
      Ω.Nonempty → IsClosedJordanCurve (frontier Ω) → κ '' Icc 0 1 ⊆ frontier Ω →
      Ω' ⊆ U → κ '' Icc 0 1 ⊆ frontier Ω' →
      U ∩ C.D q p ⊆ Ω' → Ur ∩ C.D r p ⊆ Ω ∪ Ω' →
      (∀ x ∈ U, x ∉ κ '' Icc 0 1 → x ∈ Ω ∪ Ω') →
      AccessibleFrom (C.VR p {p, q, r}) w := by
    intro Ω Ω' hΩo hΩ'o hdisjΩ hΩU hΩne hΩJ hκΩ hΩ'U hκΩ' hqpΩ' hrsub hcover
    have hΩq : ∀ x ∈ Ω, x ∉ C.D q p := fun x hx hx' =>
      (Set.disjoint_left.1 hdisjΩ) hx (hqpΩ' ⟨hΩU hx, hx'⟩)
    have hΩJq : ∀ x ∈ Ω, x ∉ C.J p q := by
      intro x hx hx'
      have hfr : x ∈ frontier (C.D q p) := by rw [hfrqp]; exact hx'
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hfr.1 Ω hΩo hx
      exact hΩq y hy1 hy2
    have hΩpq : Ω ⊆ C.D p q := by
      intro x hx
      have hc : x ∈ (C.J p q)ᶜ := hΩJq x hx
      rw [C.compl_J p hp q hq hpq] at hc
      exact hc.resolve_right (hΩq x hx)
    have hrΩ' : Ur ∩ C.D r p ⊆ Ω' := by
      rcases hUrconn.isPreconnected.subset_or_subset hΩo hΩ'o hdisjΩ hrsub with h | h
      · exact absurd h
          (hnot Ω Ω' hΩo hΩ'o hdisjΩ hΩU hΩ'U hΩne hκΩ' hcover hΩpq hqpΩ')
      · exact h
    have hΩr : ∀ x ∈ Ω ∩ Ur, x ∉ C.D r p := fun x hx hx' =>
      (Set.disjoint_left.1 hdisjΩ) hx.1 (hrΩ' ⟨hx.2, hx'⟩)
    have hΩJr : ∀ x ∈ Ω ∩ Ur, x ∉ C.J p r := by
      intro x hx hx'
      have hfr : x ∈ frontier (C.D r p) := by rw [hfrrp]; exact hx'
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hfr.1 (Ω ∩ Ur) (hΩo.inter hUropen) hx
      exact hΩr y hy1 hy2
    have hsub : Ω ∩ Ur ⊆ C.VR p {p, q, r} := by
      intro x hx
      rw [VR_triple rfl hpq hpr]
      refine ⟨hΩpq hx.1, ?_⟩
      have hc : x ∈ (C.J p r)ᶜ := hΩJr x hx
      rw [C.compl_J p hp r hr hpr] at hc
      exact hc.resolve_right (hΩr x hx)
    have hwfr : w ∈ frontier Ω := hκΩ (Set.image_mono Ioo_subset_Icc_self hwκ)
    exact AccessibleFrom.mono hsub
      (accessibleFrom_of_jordan_domain hΩo hΩne (hUbdd.subset hΩU) hΩJ hwfr hUrnhds)
  rcases hUqp with h | h
  · refine key Ω₂ Ω₁ hΩ2o hΩ1o hΩdisj.symm hΩ2U hΩ2c.nonempty hJ2 hκ2fr hΩ1U hκ1fr h ?_
      (fun x hx hx' => (hexh ⟨hx, hx'⟩).symm)
    intro x hx
    rcases hUr_sub hx with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  · exact key Ω₁ Ω₂ hΩ1o hΩ2o hΩdisj hΩ1U hΩ1c.nonempty hJ1 hκ1fr hΩ2U hκ2fr h hUr_sub
      (fun x hx hx' => hexh ⟨hx, hx'⟩)

/-- **The construction of Fig. 8(3)** in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009), with a *joining set*.

A joining set is a preconnected subset `T` of `Ur` which avoids the crosscut and meets both
half-planes `D(q,p)` and `D(r,p)`.  Since the crosscut cuts the neighbourhood `U` into two
domains and `T` avoids it, `T` lies in one of them; as it meets `D(q,p)`, it lies in the one
containing `U ∩ D(q,p)`, and so does the part of `D(r,p)` it meets.  This is exactly the
hypothesis of `AVD.CurveSystem.access_of_crosscut_aux`. -/
theorem access_of_crosscut_join (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane}
    {U Ur : Set Plane} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUJ : IsClosedJordanCurve (frontier U)) (hUconn : IsConnected (U ∩ C.D q p))
    (hwU : w ∈ U) (hUrnhds : Ur ∈ 𝓝 w) (hUrU : Ur ⊆ U) (hUropen : IsOpen Ur)
    (hUrconn : IsConnected (Ur ∩ C.D r p))
    {κ : ℝ → Plane} (hκarc : IsArc κ) (hκ0 : κ 0 ∈ frontier U) (hκ1 : κ 1 ∈ frontier U)
    (hκne : κ 0 ≠ κ 1) (hκint : κ '' Ioo 0 1 ⊆ U) (hwκ : w ∈ κ '' Ioo 0 1)
    (hκq : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D q p) (hκr : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D r p)
    (hjoin : ∃ T : Set Plane, T ⊆ Ur \ κ '' Icc 0 1 ∧ IsPreconnected T ∧
      (T ∩ C.D q p).Nonempty ∧ (T ∩ C.D r p).Nonempty) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  refine access_of_crosscut_aux hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds
    hUrU hUropen hUrconn hκarc hκ0 hκ1 hκne hκint hwκ hκq hκr ?_
  rintro Ω Ω' hΩo hΩ'o hdisjΩ - - - - hcover hΩpq - h
  obtain ⟨T, hTsub, hTconn, ⟨z₁, hz₁T, hz₁q⟩, ⟨z₂, hz₂T, hz₂r⟩⟩ := hjoin
  have hTcover : T ⊆ Ω ∪ Ω' := fun x hx => hcover x (hUrU (hTsub hx).1) (hTsub hx).2
  have hz₂Ω : z₂ ∈ Ω := h ⟨(hTsub hz₂T).1, hz₂r⟩
  rcases hTconn.subset_or_subset hΩo hΩ'o hdisjΩ hTcover with hT | hT
  · exact notMem_D_of_mem_closure hadm hp hq hpq (subset_closure (hΩpq (hT hz₁T))) hz₁q
  · exact (Set.disjoint_left.1 hdisjΩ) hz₂Ω (hT hz₂T)

/-- **The construction of Fig. 8(3)** in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009), in the case in which the *fourth quadrant* at `w` is
non-empty: points of `D(q,p) ∩ D(r,p)` occur arbitrarily close to `w`.

Such a point, taken inside `Ur`, is a joining set all by itself — it lies off the crosscut
because the crosscut misses `D(q,p)` — so this is a special case of
`AVD.CurveSystem.access_of_crosscut_join`.  It is the hypothesis under which the
configurations BC, AD and DD of Fig. 7 are settled. -/
theorem access_of_crosscut (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane}
    {U Ur : Set Plane} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUJ : IsClosedJordanCurve (frontier U)) (hUconn : IsConnected (U ∩ C.D q p))
    (hwU : w ∈ U) (hUrnhds : Ur ∈ 𝓝 w) (hUrU : Ur ⊆ U) (hUropen : IsOpen Ur)
    (hUrconn : IsConnected (Ur ∩ C.D r p))
    {κ : ℝ → Plane} (hκarc : IsArc κ) (hκ0 : κ 0 ∈ frontier U) (hκ1 : κ 1 ∈ frontier U)
    (hκne : κ 0 ≠ κ 1) (hκint : κ '' Ioo 0 1 ⊆ U) (hwκ : w ∈ κ '' Ioo 0 1)
    (hκq : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D q p) (hκr : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D r p)
    (hfourth : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  obtain ⟨z, hzUr, hzq, hzr⟩ := hfourth Ur hUrnhds
  refine access_of_crosscut_join hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds
    hUrU hUropen hUrconn hκarc hκ0 hκ1 hκne hκint hwκ hκq hκr
    ⟨{z}, ?_, isPreconnected_singleton, ⟨z, rfl, hzq⟩, ⟨z, rfl, hzr⟩⟩
  rintro x rfl
  exact ⟨hzUr, fun hc => hκq x hc hzq⟩

/-- **The construction of Fig. 8(3)** in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009), in the case in which the two curves have a common point
`z ≠ w` arbitrarily close to `w` which the crosscut avoids.

This is the form of `AVD.CurveSystem.access_of_crosscut_join` used in the degenerate
configurations, where the two curves share a segment at `w`: a small disc around such a
common point `z` lies in `Ur` and off the crosscut, and it meets both `D(q,p)` and `D(r,p)`
because `z` lies on `J(p,q) = frontier D(q,p)` and on `J(p,r) = frontier D(r,p)`.  It is
therefore a joining set. -/
theorem access_of_crosscut_common_point (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane}
    {U Ur : Set Plane} (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUJ : IsClosedJordanCurve (frontier U)) (hUconn : IsConnected (U ∩ C.D q p))
    (hwU : w ∈ U) (hUrnhds : Ur ∈ 𝓝 w) (hUrU : Ur ⊆ U) (hUropen : IsOpen Ur)
    (hUrconn : IsConnected (Ur ∩ C.D r p))
    {κ : ℝ → Plane} (hκarc : IsArc κ) (hκ0 : κ 0 ∈ frontier U) (hκ1 : κ 1 ∈ frontier U)
    (hκne : κ 0 ≠ κ 1) (hκint : κ '' Ioo 0 1 ⊆ U) (hwκ : w ∈ κ '' Ioo 0 1)
    (hκq : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D q p) (hκr : ∀ x ∈ κ '' Icc 0 1, x ∉ C.D r p)
    {z : Plane} (hzUr : z ∈ Ur) (hzκ : z ∉ κ '' Icc 0 1) (hzq : z ∈ C.J p q)
    (hzr : z ∈ C.J p r) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hκcl : IsClosed (κ '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hκarc.cont).isClosed
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 (hUropen.sdiff hκcl) z ⟨hzUr, hzκ⟩
  have hzqcl : z ∈ closure (C.D q p) :=
    mem_closure_D_of_mem_J hadm hq hp (Ne.symm hpq) (by rw [← C.J_symm hp hq hpq]; exact hzq)
  have hzrcl : z ∈ closure (C.D r p) :=
    mem_closure_D_of_mem_J hadm hr hp (Ne.symm hpr) (by rw [← C.J_symm hp hr hpr]; exact hzr)
  exact access_of_crosscut_join hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds
    hUrU hUropen hUrconn hκarc hκ0 hκ1 hκne hκint hwκ hκq hκr
    ⟨Metric.ball z ε, hball, (convex_ball z ε).isPreconnected,
      mem_closure_iff.1 hzqcl _ Metric.isOpen_ball (Metric.mem_ball_self hε),
      mem_closure_iff.1 hzrcl _ Metric.isOpen_ball (Metric.mem_ball_self hε)⟩

/-- **Configuration BC of Fig. 7 in the proof of Lemma 8** of
Klein–Langetepe–Nilforoushan (2009).

> BC) This is the most interesting case. […] Consequently, a subsegment of `G⁺` with endpoint
> `w` must be wholly disjoint from `F⁻`.  Let `H` denote the segment of `U ∩ F⁻` adjacent to
> `w`; see Fig. 8(3).  Since `H ∩ G⁺ ⊆ F⁻ ∩ G⁺ = ∅`, segment `H`, together with parts of
> `G⁺` and `∂U`, form a simple Jordan curve encircling a domain `D`. […] Therefore, part of
> `α⁰` lies in `VR(p,S)` and is an access path for `w`.

The hypotheses are those of the configuration, in the orientation-free form used throughout
this development: the branch `F⁻` of `J(p,q)` at `w` lies in the closure of the half-plane
`D(p,r)`, the branch `G⁺` of `J(p,r)` at `w` lies in the closure of the half-plane `D(p,q)`,
the branch `G⁺` is not contained in `J(p,q)` near `w` (the non-degeneracy assumption of
footnote 8 of the paper, which is what makes the separation step available), and points of
`D(q,p) ∩ D(r,p)` — the quadrant at `w` belonging to neither of the two half-planes labelled
by `p` — occur arbitrarily close to `w`.  The last hypothesis is what distinguishes
configuration BC from configuration AA, where that quadrant is empty near `w`.

The proof follows Fig. 8(3): the segment `H` of `F⁻` from the first exit point of `J(p,q)`
back to `w`, followed by the segment of `G⁺` from `w` to the first exit point of `J(p,r)`,
is a crosscut of the neighbourhood `U` (`AVD.CurveSystem.exists_crosscut_arc`, whose
hypothesis is the separation step `AVD.CurveSystem.exists_branch_disjoint`), and it meets
neither `D(q,p)` — it consists of a piece of `J(p,q)` and a piece of `closure (D(p,q))` —
nor `D(r,p)` — it consists of a piece of `closure (D(p,r))` and a piece of `J(p,r)`.  The
conclusion is then `AVD.CurveSystem.access_of_crosscut`. -/
theorem bc_configuration_access (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hFb : BranchBefore f (closure (C.D p r)))
    (hGa : BranchAfter g (closure (C.D p q)))
    (hndG : ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, g x ∉ C.J p q)
    (hfourth : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p) :
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
  refine access_of_crosscut hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds hUrU
    hUropen hUrconn hκarc (by rw [hκ0]; exact hfa) (by rw [hκ1]; exact hgb)
    (by rw [hκ0, hκ1]; exact hfane) hκint hwκ ?_ ?_ hfourth
  · intro x hx
    rw [hκimg] at hx
    rcases hx with ⟨s, -, rfl⟩ | ⟨t, ht, rfl⟩
    · intro hc
      have : f s ∈ (C.J p q)ᶜ := by rw [C.compl_J p hp q hq hpq]; exact Or.inr hc
      exact this (by rw [← hf.1.2.2.1]; exact mem_range_self s)
    · refine notMem_D_of_mem_closure hadm hp hq hpq ?_
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hg.2]; exact mem_closure_D_of_mem_J hadm hp hq hpq hwq
      · exact hGsub ⟨t, ⟨h, lt_of_le_of_lt ht.2 (lt_of_le_of_lt hble hb4)⟩, rfl⟩
  · intro x hx
    rw [hκimg] at hx
    rcases hx with ⟨s, hs, rfl⟩ | ⟨t, -, rfl⟩
    · refine notMem_D_of_mem_closure hadm hp hr hpr ?_
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h, hf.2]; exact mem_closure_D_of_mem_J hadm hp hr hpr hwr
      · exact hFsub ⟨s, ⟨lt_of_lt_of_le (by linarith) hs.1, h⟩, rfl⟩
    · intro hc
      have : g t ∈ (C.J p r)ᶜ := by rw [C.compl_J p hp r hr hpr]; exact Or.inr hc
      exact this (by rw [← hg.1.2.2.1]; exact mem_range_self t)

/-- The configuration in which **both** branches of `J(p,q)` at `w` lie in the closure of
the half-plane `D(p,r)` — case **A** for `F` in the notation of Fig. 7 of
Klein–Langetepe–Nilforoushan (2009) — together with the assumption that points of
`D(q,p) ∩ D(r,p)` occur arbitrarily close to `w`.

Here the crosscut of the construction of Fig. 8(3) is simply the whole piece of `J(p,q)`
inside the neighbourhood `U`, that is, the segment `H` of the proof of Lemma 7: it lies on
`J(p,q)`, hence misses `D(q,p)`, and it lies in `closure (D(p,r))` by hypothesis, hence
misses `D(r,p)`.  The conclusion is `AVD.CurveSystem.access_of_crosscut`. -/
theorem access_of_both_branches_f (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane} {f g : ℝ → Plane}
    (hf : IsProperLineParamAt f (C.J p q) w) (hg : IsProperLineParamAt g (C.J p r) w)
    (hFb : BranchBefore f (closure (C.D p r))) (hFa : BranchAfter f (closure (C.D p r)))
    (hfourth : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hwr : w ∈ C.J p r := by rw [← hg.2, ← hg.1.2.2.1]; exact mem_range_self 0
  obtain ⟨δ1, hδ1, hsub1⟩ := hFb
  obtain ⟨δ2, hδ2, hsub2⟩ := hFa
  have hmin : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  set δ₀ : ℝ := min δ1 δ2 / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  have hb1 : δ₀ < δ1 := by have h := min_le_left δ1 δ2; rw [hδ₀def]; linarith
  have hb2 : δ₀ < δ2 := by have h := min_le_right δ1 δ2; rw [hδ₀def]; linarith
  obtain ⟨U, Ur, hUopen, hUbdd, hUJ, hUconn, hwU, hboundf, -, hUrnhds, hUrU, hUropen,
    hUrconn⟩ := exists_crosscut_nbhds hadm hp hq hr hpq hpr hf hg hδ₀
  obtain ⟨a, ha, hfU, hfa⟩ :=
    hf.1.exists_first_exit_neg hUopen hUbdd (by rw [hf.2]; exact hwU)
  obtain ⟨c, hc, hfU', hfc⟩ :=
    hf.1.exists_first_exit hUopen hUbdd (by rw [hf.2]; exact hwU)
  have hage : -δ₀ ≤ a := by
    by_contra hcon
    push Not at hcon
    have h := hboundf _ (hfU ⟨-δ₀, ⟨hcon, by linarith⟩, rfl⟩)
    rw [abs_of_nonpos (by linarith)] at h
    linarith
  have hcle : c ≤ δ₀ := by
    by_contra hcon
    push Not at hcon
    have h := hboundf _ (hfU' ⟨δ₀, ⟨hδ₀.le, hcon⟩, rfl⟩)
    rw [abs_of_nonneg hδ₀.le] at h
    linarith
  have hac : a < c := lt_trans ha hc
  have hκIoo : subarcParam f a c '' Ioo 0 1 = f '' Ioo a c := subarcParam_image_Ioo hac
  have hκIcc : subarcParam f a c '' Icc 0 1 = f '' Icc a c := subarcParam_image hac.le
  have hIooU : f '' Ioo a c ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    rcases le_or_gt t 0 with h | h
    · exact hfU ⟨t, ⟨ht.1, h⟩, rfl⟩
    · exact hfU' ⟨t, ⟨h.le, ht.2⟩, rfl⟩
  refine access_of_crosscut hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds hUrU
    hUropen hUrconn (isArc_subarcParam hf.1.1 hf.1.2.1 hac) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfourth
  · rw [subarcParam_zero]; exact hfa
  · rw [subarcParam_one]; exact hfc
  · rw [subarcParam_zero, subarcParam_one]
    intro hcon
    have : a = c := hf.1.2.1 hcon
    linarith
  · rw [hκIoo]; exact hIooU
  · rw [hκIoo]; exact ⟨0, ⟨ha, hc⟩, hf.2⟩
  · intro x hx
    rw [hκIcc] at hx
    obtain ⟨t, -, rfl⟩ := hx
    intro hcm
    have : f t ∈ (C.J p q)ᶜ := by rw [C.compl_J p hp q hq hpq]; exact Or.inr hcm
    exact this (by rw [← hf.1.2.2.1]; exact mem_range_self t)
  · intro x hx
    rw [hκIcc] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine notMem_D_of_mem_closure hadm hp hr hpr ?_
    rcases lt_trichotomy t 0 with h | h | h
    · exact hsub1 ⟨t, ⟨lt_of_lt_of_le (by linarith) ht.1, h⟩, rfl⟩
    · rw [h, hf.2]; exact mem_closure_D_of_mem_J hadm hp hr hpr hwr
    · exact hsub2 ⟨t, ⟨h, lt_of_le_of_lt ht.2 (by linarith)⟩, rfl⟩

/-- The configuration in which **both** branches of `J(p,r)` at `w` lie in the closure of
the half-plane `D(p,q)` — case **A** for `G` in the notation of Fig. 7 of
Klein–Langetepe–Nilforoushan (2009) — together with the assumption that points of
`D(q,p) ∩ D(r,p)` occur arbitrarily close to `w`.

This is `AVD.CurveSystem.access_of_both_branches_f` with the roles of the two curves
exchanged: the crosscut is the whole piece of `J(p,r)` inside the neighbourhood `U`, which
misses `D(r,p)` because it lies on `J(p,r)` and misses `D(q,p)` because it lies in
`closure (D(p,q))`. -/
theorem access_of_both_branches_g (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane} {f g : ℝ → Plane}
    (hf : IsProperLineParamAt f (C.J p q) w) (hg : IsProperLineParamAt g (C.J p r) w)
    (hGb : BranchBefore g (closure (C.D p q))) (hGa : BranchAfter g (closure (C.D p q)))
    (hfourth : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.D q p ∩ C.D r p) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hwq : w ∈ C.J p q := by rw [← hf.2, ← hf.1.2.2.1]; exact mem_range_self 0
  obtain ⟨δ1, hδ1, hsub1⟩ := hGb
  obtain ⟨δ2, hδ2, hsub2⟩ := hGa
  have hmin : 0 < min δ1 δ2 := lt_min hδ1 hδ2
  set δ₀ : ℝ := min δ1 δ2 / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; linarith
  have hb1 : δ₀ < δ1 := by have h := min_le_left δ1 δ2; rw [hδ₀def]; linarith
  have hb2 : δ₀ < δ2 := by have h := min_le_right δ1 δ2; rw [hδ₀def]; linarith
  obtain ⟨U, Ur, hUopen, hUbdd, hUJ, hUconn, hwU, -, hboundg, hUrnhds, hUrU, hUropen,
    hUrconn⟩ := exists_crosscut_nbhds hadm hp hq hr hpq hpr hf hg hδ₀
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
  refine access_of_crosscut hadm hp hq hr hpq hpr hUopen hUbdd hUJ hUconn hwU hUrnhds hUrU
    hUropen hUrconn (isArc_subarcParam hg.1.1 hg.1.2.1 hac) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfourth
  · rw [subarcParam_zero]; exact hga
  · rw [subarcParam_one]; exact hgc
  · rw [subarcParam_zero, subarcParam_one]
    intro hcon
    have : a = c := hg.1.2.1 hcon
    linarith
  · rw [hκIoo]; exact hIooU
  · rw [hκIoo]; exact ⟨0, ⟨ha, hc⟩, hg.2⟩
  · intro x hx
    rw [hκIcc] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    refine notMem_D_of_mem_closure hadm hp hq hpq ?_
    rcases lt_trichotomy t 0 with h | h | h
    · exact hsub1 ⟨t, ⟨lt_of_lt_of_le (by linarith) ht.1, h⟩, rfl⟩
    · rw [h, hg.2]; exact mem_closure_D_of_mem_J hadm hp hq hpq hwq
    · exact hsub2 ⟨t, ⟨h, lt_of_le_of_lt ht.2 (by linarith)⟩, rfl⟩
  · intro x hx
    rw [hκIcc] at hx
    obtain ⟨t, -, rfl⟩ := hx
    intro hcm
    have : g t ∈ (C.J p r)ᶜ := by rw [C.compl_J p hp r hr hpr]; exact Or.inr hcm
    exact this (by rw [← hg.1.2.2.1]; exact mem_range_self t)

end CurveSystem

end AVD
