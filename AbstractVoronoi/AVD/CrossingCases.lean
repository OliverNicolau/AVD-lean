import AbstractVoronoi.Jordan.PlaneTools
import AbstractVoronoi.Paper.Lemma7

/-!
# The configurations of Fig. 7 in the proof of Lemma 8

The case analysis of the proof of Lemma 8 of R. Klein, E. Langetepe, Z. Nilforoushan,
*Abstract Voronoi diagrams revisited*, Computational Geometry 42 (2009) 885–902, for a
boundary point lying on both bisecting curves: the configurations AD, DD, DA of Fig. 7 are
proved here (`AVD.CurveSystem.lemma8_of_branches`), together with the two ingredients of the
remaining configurations — the separation of the two curves near the boundary point
(`AVD.CurveSystem.exists_branch_disjoint`) and the crosscut of Fig. 8(3)
(`AVD.CurveSystem.exists_crosscut_arc`).  The configurations AA and BC themselves are
settled in `AbstractVoronoi.AVD.BCConfiguration`, `AbstractVoronoi.AVD.SharedSegment` and
`AbstractVoronoi.AVD.AAConfiguration`.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- Every point of a bisecting curve is the base point of a proper parametrization of that
curve: axiom `A₁` provides a proper parametrization, which is then shifted in the
parameter.  This is the situation `g(0) = w` of the discussion preceding Lemma 7 of
Klein–Langetepe–Nilforoushan (2009). -/
theorem exists_properLineParamAt (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {w : Plane} (hw : w ∈ C.J p q) :
    ∃ g : ℝ → Plane, IsProperLineParamAt g (C.J p q) w := by
  obtain ⟨g, hcont, hinj, hrange, hproper⟩ := (hadm.A1 p hp q hq hpq).exists_properParam
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, g t₀ = w := by rw [← hrange] at hw; exact hw
  refine ⟨fun t => g (t + t₀), ⟨hcont.comp (by fun_prop), ?_, ?_, ?_⟩, by simpa using ht₀⟩
  · intro a b hab
    have := hinj hab
    linarith
  · apply Subset.antisymm
    · rintro x ⟨t, rfl⟩
      rw [← hrange]
      exact ⟨t + t₀, rfl⟩
    · intro x hx
      rw [← hrange] at hx
      obtain ⟨t, rfl⟩ := hx
      exact ⟨t - t₀, by ring_nf⟩
  · intro K hK
    exact (Homeomorph.isCompact_preimage (Homeomorph.addRight t₀)).2 (hproper K hK)

/-- The easy configurations in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009): if both branches of `J(p,r)` at `w` stay in the closure
of the half-plane `D(q,p)`, then

> an arc accessing `w` from `D(p,q)` is also contained in `D(p,r)`, after shortening, hence
> in `VR(p,S)`.

Indeed, near `w` the curve `J(p,r)` avoids the open half-plane `D(p,q)`, so an access arc
of `w` inside a small neighbourhood `U` of `w` and inside `D(p,q)` (Theorem 4) never meets
`J(p,r)`; being connected, it stays in one of the two half-planes of `J(p,r)`, and it is the
right one as soon as the arc is started at a point of `VR(p, {p,q,r})`, which exists
arbitrarily close to `w` because `w` lies on the boundary of that region.

This covers the configurations AD and DD of Fig. 7 of the paper, and — after exchanging the
roles of `q` and `r` — also DA. -/
theorem lemma8_of_branches (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) {w : Plane} (hwq : w ∈ C.J p q)
    (hw : w ∈ frontier (C.VR p {p, q, r})) {g : ℝ → Plane}
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hGb : BranchBefore g (closure (C.D q p))) (hGa : BranchAfter g (closure (C.D q p))) :
    AccessibleFrom (C.VR p {p, q, r}) w := by
  have hVR : C.VR p {p, q, r} = C.D p q ∩ C.D p r := VR_triple rfl hpq hpr
  -- a neighbourhood of `w` in which `J(p,r)` stays in the closure of `D(q,p)`
  obtain ⟨δ₁, hδ₁, hsub₁⟩ := hGb
  obtain ⟨δ₂, hδ₂, hsub₂⟩ := hGa
  obtain ⟨W, hWopen, hwW, hWsub⟩ := hg.1.exists_nbhd (lt_min hδ₁ hδ₂)
  rw [hg.2] at hwW
  -- Theorem 4 for `J(p,q)` at `w`, inside `W`
  obtain ⟨-, hacc⟩ := exists_theorem4_data hadm hp hq hpq
  obtain ⟨U, hUnhds, hUW, -, -, haccess⟩ := hacc w hwq W (hWopen.mem_nhds hwW)
  -- a point of the Voronoi region close to `w`
  have hwcl : w ∈ closure (C.VR p {p, q, r}) := frontier_subset_closure hw
  obtain ⟨x, hxU, hxVR⟩ := mem_closure_iff_nhds.1 hwcl U hUnhds
  have hxD : x ∈ C.D p q := (hVR ▸ hxVR).1
  obtain ⟨α, harc, hα0, hα1, hαsub⟩ := haccess x ⟨hxU, hxD⟩
  refine ⟨α, harc, hα1, ?_⟩
  -- the access arc misses `J(p,r)`
  have hmissJ : ∀ y ∈ α '' Ico 0 1, y ∉ C.J p r := by
    intro y hy hyJ
    obtain ⟨hyU, hyD⟩ := hαsub hy
    have hyW : y ∈ W := hUW hyU
    obtain ⟨c, hc, hcy⟩ := hWsub ⟨hyJ, hyW⟩
    have hycl : y ∈ closure (C.D q p) := by
      rcases lt_trichotomy c 0 with hc0 | rfl | hc0
      · exact hsub₁ ⟨c, ⟨by linarith [hc.1, min_le_left δ₁ δ₂], hc0⟩, hcy⟩
      · -- `y = w` is impossible: `w` lies on `J(p,q)`, while `y ∈ D(p,q)`
        exfalso
        rw [← hcy, hg.2] at hyD
        exact (notMem_D_of_mem_J hp hq hpq hwq).1 hyD
      · exact hsub₂ ⟨c, ⟨hc0, by linarith [hc.2, min_le_right δ₁ δ₂]⟩, hcy⟩
    have : y ∉ closure (C.D q p) := by
      rw [closure_D_eq hadm hq hp (Ne.symm hpq)]
      rintro (h | h)
      · exact (Set.disjoint_left.1 (C.D_disjoint p hp q hq hpq)) hyD h
      · exact (notMem_D_of_mem_J hp hq hpq (by rwa [← C.J_symm hq hp (Ne.symm hpq)])).1 hyD
    exact this hycl
  -- hence, being connected, it stays in the half-plane `D(p,r)` containing its start point
  have hconn : IsPreconnected (α '' Ico 0 1) :=
    (isPreconnected_Ico).image α (harc.cont.mono (Ico_subset_Icc_self))
  have hcover : α '' Ico 0 1 ⊆ C.D p r ∪ C.D r p := by
    intro y hy
    have : y ∈ (C.J p r)ᶜ := hmissJ y hy
    rwa [C.compl_J p hp r hr hpr] at this
  have hstart : α 0 ∈ α '' Ico 0 1 := ⟨0, ⟨le_refl 0, one_pos⟩, rfl⟩
  have hxDr : α 0 ∈ C.D p r := by rw [hα0]; exact (hVR ▸ hxVR).2
  have hsubDr : α '' Ico 0 1 ⊆ C.D p r := by
    rcases hconn.subset_or_subset (C.D_isOpen p hp r hr hpr)
      (C.D_isOpen r hr p hp (Ne.symm hpr))
      (C.D_disjoint p hp r hr hpr) hcover with h | h
    · exact h
    · exact absurd (h hstart) (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr) hxDr)
  intro y hy
  rw [hVR]
  exact ⟨(hαsub hy).2, hsubDr hy⟩

/-- A preconnected set that meets an open set `V` and misses the frontier of `V` is
contained in `V`.  A convenient form of connectedness, used in the analysis of
configuration AA of Fig. 7 of Klein–Langetepe–Nilforoushan (2009). -/
theorem subset_of_preconnected_of_disjoint_frontier {N V : Set Plane} (hN : IsPreconnected N)
    (hV : IsOpen V) (hdisj : Disjoint N (frontier V)) {x : Plane} (hxN : x ∈ N)
    (hxV : x ∈ V) : N ⊆ V := by
  have hcover : N ⊆ V ∪ (closure V)ᶜ := by
    intro y hy
    by_cases h : y ∈ closure V
    · refine Or.inl ?_
      by_contra hc
      exact (Set.disjoint_left.1 hdisj) hy ⟨h, by rwa [hV.interior_eq]⟩
    · exact Or.inr h
  have hdis : Disjoint V ((closure V)ᶜ) :=
    Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
  rcases hN.subset_or_subset hV isClosed_closure.isOpen_compl hdis hcover with h | h
  · exact h
  · exact absurd (h hxN) (fun hc => hc (subset_closure hxV))

/-- The trapping lemma behind configuration **AA** of Fig. 7 in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009).

Assume that the two branches `G⁻, G⁺` of `J(p,r)` at the common point `w` of `J(p,q)` and
`J(p,r)` lie in the open half-plane `D(p,q)`.  Then there is a radius `ε > 0` such that any
point `f t₀` of `J(p,q)` with `|t₀| < ε` lying in the open half-plane `D(p,r)` is *trapped*:
every connected piece of `J(p,q)` that contains it and avoids `w` is bounded.

This is the formal content of the argument of the paper for configuration AA,

> AA) Here the Voronoi region of `p` would be disconnected.  Formally, we could find points
> `a, b ∈ D(p,q)` on `G⁺` and `G⁻`, respectively, and connect them with paths
> `π ⊆ VR(p,S)` and `ρ ⊆ VR(r,S)` as in the proof of Lemma 6.  The arguments presented
> there show that the domain `D` bounded by these paths must contain point `w`, so that `ρ`
> has to pass above `w` while `π` stays below `J(p,q)`.  This is in conflict with the
> supposed orientation of `J(p,r)` at `w`,

with the appeal to the orientation of `J(p,r)` at `w` replaced by a connectedness argument
that needs no orientation convention.  The two points `a = g u` and `b = g v` are taken on
the two branches, and `AVD.CurveSystem.exists_lemma6_jordan_domain` — the first half of the
proof of Lemma 6 — provides the arcs `π, ρ`, the bounded domain `Dm` they bound, and the
position of the three pieces of `J(p,r)`: the piece `g((u,v))` through `w` lies in `Dm`,
the two unbounded pieces lie outside.  Let `V` be the connected component of
`Dm ∖ g([u,v])` containing `f t₀`.  Then `V ⊆ D(p,r)` and `V ⊆ Dm` is bounded, and a
connected piece of `J(p,q)` through `f t₀` avoiding `w` cannot leave `V`: its frontier is
contained in `π ∪ ρ ∪ g([u,v])`, and none of these three sets contains a point of `J(p,q)`
other than `w`.  Indeed `π` and `g([u,v]) ∖ {w}` lie in `D(p,q)`, the endpoints of `ρ` are
`g u, g v ∈ D(p,q)`, and the relative interior of `ρ` lies in `D(r,p)`, which is disjoint
from the closure of `D(p,r)` and hence from the closure of `V`. -/
theorem exists_trapping_radius (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hGb : BranchBefore g (C.D p q)) (hGa : BranchAfter g (C.D p q)) :
    ∃ ε > (0 : ℝ), ∀ t₀ : ℝ, |t₀| < ε → f t₀ ∈ C.D p r →
      ∀ N : Set ℝ, IsPreconnected N → (0 : ℝ) ∉ N → t₀ ∈ N →
        Bornology.IsBounded (f '' N) := by
  obtain ⟨hfcont, hfinj, hfrange, hfproper⟩ := hf.1
  have hf0 : f 0 = w := hf.2
  obtain ⟨hgcont, hginj, hgrange, hgproper⟩ := hg.1
  have hg0 : g 0 = w := hg.2
  obtain ⟨δ₁, hδ₁, hsub₁⟩ := hGb
  obtain ⟨δ₂, hδ₂, hsub₂⟩ := hGa
  set u : ℝ := -δ₁ / 2 with hudef
  set v : ℝ := δ₂ / 2 with hvdef
  have hu0 : u < 0 := by rw [hudef]; linarith
  have hv0 : (0 : ℝ) < v := by rw [hvdef]; linarith
  have huv : u < v := hu0.trans hv0
  -- the two branches of `J(p,r)` at `w`, without `w` itself, lie in `D(p,q)`
  have hbranch : ∀ c ∈ Icc u v, c ≠ 0 → g c ∈ C.D p q := by
    intro c hc hc0
    rcases lt_or_gt_of_ne hc0 with h | h
    · exact hsub₁ ⟨c, ⟨by rw [hudef] at hc; linarith [hc.1], h⟩, rfl⟩
    · exact hsub₂ ⟨c, ⟨h, by rw [hvdef] at hc; linarith [hc.2]⟩, rfl⟩
  have hgu : g u ∈ C.D p q := hbranch u ⟨le_refl u, huv.le⟩ (ne_of_lt hu0)
  have hgv : g v ∈ C.D p q := hbranch v ⟨huv.le, le_refl v⟩ (ne_of_gt hv0)
  -- the closed Jordan curve of the proof of Lemma 6
  obtain ⟨π, ρ, Dm, Em, -, hπ0, hπ1, hπint, -, hρ0, hρ1, hρint, hODm, -, -, hdDE, hun,
    hfrDm, hbDm, hmid, hIio, hIoi⟩ :=
    exists_lemma6_jordan_domain hadm hp hq hr hpq hqr hpr
      ⟨hgcont, hginj, hgrange, hgproper⟩ huv hgu hgv
  have hVRp : C.VR p {p, q, r} = C.D p q ∩ C.D p r := VR_triple rfl hpq hpr
  have hVRr : C.VR r {p, q, r} = C.D r p ∩ C.D r q :=
    VR_triple (by ext x; simp; tauto) (Ne.symm hpr) (Ne.symm hqr)
  -- the piece of `J(p,r)` between the two points, and its properties
  set M : Set Plane := g '' Icc u v with hMdef
  have hMclosed : IsClosed M := (isCompact_Icc.image hgcont).isClosed
  have hMJ : M ⊆ C.J p r := by
    rintro _ ⟨c, -, rfl⟩
    exact hgrange ▸ mem_range_self c
  have hMDpq : ∀ y ∈ M, y ≠ w → y ∈ C.D p q := by
    rintro _ ⟨c, hc, rfl⟩ hne
    exact hbranch c hc fun h => hne (by rw [h, hg0])
  have hwDm : w ∈ Dm := by
    have := hmid ⟨0, ⟨hu0, hv0⟩, rfl⟩
    rwa [hg0] at this
  have hJDm : ∀ y ∈ C.J p r, y ∈ Dm → y ∈ M := by
    intro y hy hyD
    rw [← hgrange] at hy
    obtain ⟨c, rfl⟩ := hy
    rcases lt_trichotomy c u with hc | hc | hc
    · exact absurd (hIio ⟨c, hc, rfl⟩) (Set.disjoint_left.1 hdDE hyD)
    · exact ⟨c, ⟨hc.ge, by rw [hc]; exact huv.le⟩, rfl⟩
    · rcases le_or_gt c v with hc' | hc'
      · exact ⟨c, ⟨hc.le, hc'⟩, rfl⟩
      · exact absurd (hIoi ⟨c, hc', rfl⟩) (Set.disjoint_left.1 hdDE hyD)
  -- the arcs `π` and `ρ`
  have hπIcc : π '' Icc 0 1 ⊆ C.D p q := by
    rintro _ ⟨c, hc, rfl⟩
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h, hπ0]; exact hgu
    · rcases eq_or_lt_of_le hc.2 with h' | h'
      · rw [h', hπ1]; exact hgv
      · exact (hVRp ▸ hπint ⟨c, ⟨h, h'⟩, rfl⟩ : π c ∈ C.D p q ∩ C.D p r).1
  have hρIcc : ρ '' Icc 0 1 ⊆ C.D p q ∪ C.D r p := by
    rintro _ ⟨c, hc, rfl⟩
    rcases eq_or_lt_of_le hc.1 with h | h
    · exact Or.inl (by rw [← h, hρ0]; exact hgu)
    · rcases eq_or_lt_of_le hc.2 with h' | h'
      · exact Or.inl (by rw [h', hρ1]; exact hgv)
      · exact Or.inr (hVRr ▸ hρint ⟨c, ⟨h, h'⟩, rfl⟩ : ρ c ∈ C.D r p ∩ C.D r q).1
  -- the open set whose component traps the curve, and the bound on its frontier
  set O : Set Plane := Dm \ M with hOdef
  have hOopen : IsOpen O := hODm.sdiff hMclosed
  have hfrO : frontier O ⊆ (π '' Icc 0 1 ∪ ρ '' Icc 0 1) ∪ M := by
    have h1 : frontier O ⊆ frontier Dm ∪ frontier M := by
      rw [hOdef, Set.sdiff_eq]
      refine (frontier_inter_subset Dm Mᶜ).trans ?_
      rw [frontier_compl]
      intro y hy
      rcases hy with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    intro y hy
    rcases h1 hy with h | h
    · exact Or.inl (hfrDm ▸ h)
    · exact Or.inr (hMclosed.frontier_subset h)
  -- a radius inside which the points of `J(p,q)` lie in `Dm`
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > (0 : ℝ), ∀ c : ℝ, |c| < ε → f c ∈ Dm := by
    have hmem : f ⁻¹' Dm ∈ 𝓝 (0 : ℝ) :=
      hfcont.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hODm.mem_nhds hwDm)
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 hmem
    exact ⟨ε, hε, fun c hc => hsub (by simpa [Real.dist_eq] using hc)⟩
  refine ⟨ε, hε, ?_⟩
  intro t₀ ht₀abs ht₀Dpr N hNconn h0N ht₀N
  have ht₀Dm : f t₀ ∈ Dm := hεsub _ ht₀abs
  have ht₀O : f t₀ ∈ O :=
    ⟨ht₀Dm, fun hm => (notMem_D_of_mem_J hp hr hpr (hMJ hm)).1 ht₀Dpr⟩
  set V : Set Plane := connectedComponentIn O (f t₀) with hVdef
  have hVopen : IsOpen V := hOopen.connectedComponentIn
  have hVsub : V ⊆ O := connectedComponentIn_subset O _
  have hxV : f t₀ ∈ V := mem_connectedComponentIn ht₀O
  have hVDpr : V ⊆ C.D p r := by
    have hcover : V ⊆ C.D p r ∪ C.D r p := by
      intro y hy
      have hyJ : y ∉ C.J p r := fun hJ => (hVsub hy).2 (hJDm y hJ (hVsub hy).1)
      have h' : y ∈ (C.J p r)ᶜ := hyJ
      rwa [C.compl_J p hp r hr hpr] at h'
    rcases isPreconnected_connectedComponentIn.subset_or_subset
      (C.D_isOpen p hp r hr hpr) (C.D_isOpen r hr p hp (Ne.symm hpr))
      (C.D_disjoint p hp r hr hpr) hcover with h | h
    · exact h
    · exact absurd (h hxV) (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr) ht₀Dpr)
  -- the frontier of `V` contains no point of `J(p,q)` other than `w`
  have hfrontier : Disjoint (f '' N) (frontier V) := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, hcN, rfl⟩ hyfr
    have hyJpq : f c ∈ C.J p q := hfrange ▸ mem_range_self c
    have hyw : f c ≠ w := by
      intro h
      refine h0N ?_
      have hc0 : c = 0 := hfinj (by rw [h, hf0])
      rwa [hc0] at hcN
    have hynotDpq : f c ∉ C.D p q := (notMem_D_of_mem_J hp hq hpq hyJpq).1
    rcases hfrO (frontier_connectedComponentIn_subset hOopen hyfr) with (h | h) | h
    · exact hynotDpq (hπIcc h)
    · rcases hρIcc h with h' | h'
      · exact hynotDpq h'
      · have hycl : f c ∈ closure (C.D p r) := closure_mono hVDpr hyfr.1
        rw [closure_D_eq hadm hp hr hpr] at hycl
        rcases hycl with h'' | h''
        · exact (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) h'' h'
        · exact (notMem_D_of_mem_J hp hr hpr h'').2 h'
    · exact hynotDpq (hMDpq _ h hyw)
  -- hence the piece of `J(p,q)` stays inside the bounded set `V`
  have hsubV : f '' N ⊆ V :=
    subset_of_preconnected_of_disjoint_frontier (hNconn.image f hfcont.continuousOn) hVopen
      hfrontier (mem_image_of_mem f ht₀N) hxV
  exact hbDm.subset (hsubV.trans (hVsub.trans fun y hy => hy.1))

/-- **Configuration AA of Fig. 7** in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009) is impossible.

In configuration AA the two branches `G⁻, G⁺` of `J(p,r)` at the common point `w` lie in
the half-plane `D(p,q)`, and the two branches `F⁻, F⁺` of `J(p,q)` lie in `D(p,r)`; the
hypotheses below assume the former for both branches and the latter for one of the two
branches, which is all that the argument needs.

The proof is the paper's argument for AA, in the orientation-free form of
`AVD.CurveSystem.exists_trapping_radius`: the branch of `J(p,q)` lying in `D(p,r)` provides
a point `f t₀` arbitrarily close to `w` which is trapped in a bounded domain, while the
half curve of `J(p,q)` containing it and avoiding `w` is unbounded, `f` being a proper
parametrization. -/
theorem aa_configuration_impossible (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hGb : BranchBefore g (C.D p q)) (hGa : BranchAfter g (C.D p q))
    (hF : BranchBefore f (C.D p r) ∨ BranchAfter f (C.D p r)) : False := by
  obtain ⟨ε, hε, htrap⟩ := exists_trapping_radius hadm hp hq hr hpq hqr hpr hf hg hGb hGa
  -- a half curve of a proper parametrization is unbounded
  have hunb : ∀ N : Set ℝ, (¬ BddBelow N ∨ ¬ BddAbove N) →
      ¬ Bornology.IsBounded (f '' N) := by
    intro N hN hb
    have hcomp : IsCompact (f ⁻¹' closure (f '' N)) := hf.1.2.2.2 _ hb.isCompact_closure
    have hNsub : N ⊆ f ⁻¹' closure (f '' N) := fun c hc => subset_closure ⟨c, hc, rfl⟩
    rcases hN with h | h
    · exact h (BddBelow.mono hNsub hcomp.bddBelow)
    · exact h (BddAbove.mono hNsub hcomp.bddAbove)
  rcases hF with ⟨δ, hδ, hsub⟩ | ⟨δ, hδ, hsub⟩
  · have hmin := lt_min hδ hε
    refine hunb (Iio 0) (Or.inl (not_bddBelow_Iio 0))
      (htrap (-(min δ ε) / 2) ?_ ?_ (Iio 0) isPreconnected_Iio (by simp) (by
        simp only [mem_Iio]; linarith))
    · rw [abs_of_nonpos (by linarith)]
      have := min_le_right δ ε
      linarith
    · exact hsub ⟨-(min δ ε) / 2, ⟨by have := min_le_left δ ε; linarith, by linarith⟩, rfl⟩
  · have hmin := lt_min hδ hε
    refine hunb (Ioi 0) (Or.inr (not_bddAbove_Ioi 0))
      (htrap (min δ ε / 2) ?_ ?_ (Ioi 0) isPreconnected_Ioi (by simp) (by
        simp only [mem_Ioi]; linarith))
    · rw [abs_of_nonneg (by linarith)]
      have := min_le_right δ ε
      linarith
    · exact hsub ⟨min δ ε / 2, ⟨by linarith, by have := min_le_left δ ε; linarith⟩, rfl⟩

/-- **No connected piece of `J(p,q)` on the `p`-side of `J(p,r)` can cross the Jordan curve
of the proof of Lemma 6.**

Let `g u`, `g v` be two points of `J(p,r)` lying in the open half-plane `D(p,q)`, and let
`K` be a preconnected set of points of `J(p,q)` all lying in the closure of the half-plane
`D(p,r)`.  Then `K` cannot contain at the same time a point `g s` of `J(p,r)` strictly
between `g u` and `g v` and a point `g t` of one of the two unbounded pieces of `J(p,r)`.

Indeed, `AVD.CurveSystem.exists_lemma6_jordan_domain` provides the closed Jordan curve
`π ∪ ρ` of the proof of **Lemma 6** of Klein–Langetepe–Nilforoushan (2009) through `g u` and
`g v`, whose bounded complementary domain contains `g s` while `g t` lies in the unbounded
one; the connected set `K` would have to meet that curve.  But `K` cannot meet `π`, which
lies in `D(p,q)` — its relative interior even lies in `VR(p,{p,q,r})`, and its two endpoints
are `g u` and `g v` — because `K ⊆ J(p,q)`; and it cannot meet `ρ`, whose endpoints are
again `g u`, `g v` and whose relative interior lies in `VR(r,{p,q,r}) ⊆ D(r,p)`, a set
disjoint from the closure of `D(p,r)`.

This is the argument which the paper, in case **BC** of the proof of Lemma 8, invokes as
"the same formal proof as for AA". -/
theorem no_preconnected_crossing (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p r))
    {u v : ℝ} (huv : u < v) (hgu : g u ∈ C.D p q) (hgv : g v ∈ C.D p q)
    {K : Set Plane} (hKconn : IsPreconnected K) (hKJ : K ⊆ C.J p q)
    (hKcl : K ⊆ closure (C.D p r))
    {s t : ℝ} (hs : s ∈ Ioo u v) (hsK : g s ∈ K) (ht : t < u ∨ v < t) (htK : g t ∈ K) :
    False := by
  obtain ⟨π, ρ, Dm, Em, -, hπ0, hπ1, hπint, -, hρ0, hρ1, hρint, hODm, hOEm, -, hdDE, hun,
    -, -, hmid, hIio, hIoi⟩ :=
    exists_lemma6_jordan_domain hadm hp hq hr hpq hqr hpr hg huv hgu hgv
  have hVRp : C.VR p {p, q, r} = C.D p q ∩ C.D p r := VR_triple rfl hpq hpr
  have hVRr : C.VR r {p, q, r} = C.D r p ∩ C.D r q :=
    VR_triple (by ext x; simp; tauto) (Ne.symm hpr) (Ne.symm hqr)
  have hsDm : g s ∈ Dm := hmid ⟨s, hs, rfl⟩
  have htEm : g t ∈ Em := by
    rcases ht with h | h
    · exact hIio ⟨t, h, rfl⟩
    · exact hIoi ⟨t, h, rfl⟩
  -- the connected set `K` must meet the closed Jordan curve `π ∪ ρ`
  have hmeet : ∃ y ∈ K, y ∈ π '' Icc 0 1 ∪ ρ '' Icc 0 1 := by
    by_contra hcon
    push Not at hcon
    have hcover : K ⊆ Dm ∪ Em := by
      intro y hy
      have hy' : y ∈ (π '' Icc 0 1 ∪ ρ '' Icc 0 1)ᶜ := hcon y hy
      rwa [← hun] at hy'
    obtain ⟨y, -, hy⟩ := hKconn Dm Em hODm hOEm hcover ⟨g s, hsK, hsDm⟩ ⟨g t, htK, htEm⟩
    exact (Set.disjoint_left.1 hdDE) hy.1 hy.2
  obtain ⟨y, hyK, hyΓ⟩ := hmeet
  have hynotDpq : y ∉ C.D p q := (notMem_D_of_mem_J hp hq hpq (hKJ hyK)).1
  rcases hyΓ with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · refine hynotDpq ?_
    rcases eq_or_lt_of_le hc.1 with h | h
    · rw [← h, hπ0]; exact hgu
    · rcases eq_or_lt_of_le hc.2 with h' | h'
      · rw [h', hπ1]; exact hgv
      · exact (hVRp ▸ hπint ⟨c, ⟨h, h'⟩, rfl⟩ : π c ∈ C.D p q ∩ C.D p r).1
  · rcases eq_or_lt_of_le hc.1 with h | h
    · exact hynotDpq (by rw [← h, hρ0]; exact hgu)
    · rcases eq_or_lt_of_le hc.2 with h' | h'
      · exact hynotDpq (by rw [h', hρ1]; exact hgv)
      · have hrp : ρ c ∈ C.D r p :=
          (hVRr ▸ hρint ⟨c, ⟨h, h'⟩, rfl⟩ : ρ c ∈ C.D r p ∩ C.D r q).1
        have hycl : ρ c ∈ closure (C.D p r) := hKcl hyK
        rw [closure_D_eq hadm hp hr hpr] at hycl
        rcases hycl with h'' | h''
        · exact (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) h'' hrp
        · exact (notMem_D_of_mem_J hp hr hpr h'').2 hrp

/-- **A subsegment of `G⁺` at `w` is disjoint from `F⁻`**, the first step of the analysis of
configuration **BC** of Fig. 7 in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009):

> Thus, all points of `F⁻` encountered on the backward walk along `G⁺` towards `w`, must be
> situated in the same order on both oriented segments, `F⁻` and `G⁺` […].  Consequently, a
> subsegment of `G⁺` with endpoint `w` must be wholly disjoint from `F⁻`.

The hypotheses are those of configuration BC: the branch `F⁻` of `J(p,q)` before `w` lies in
the closure of `D(p,r)`, the branch `G⁺` of `J(p,r)` after `w` lies in the closure of
`D(p,q)`, and `G⁺` is not, near `w`, contained in `J(p,q)` — the non-degeneracy assumption
of footnote 8, without which the two curves share a segment at `w`.

The proof does not go through the ordering argument of the paper.  It shows directly that a
common point `g s = f t` of `G⁺` and `F⁻` is impossible as soon as `G⁺` has points of the
open half-plane `D(p,q)` on both sides of it: the piece `f([t,0])` of `J(p,q)` from that
common point to `w` lies in the closure of `D(p,r)` and joins the point `g s`, which lies
inside the Jordan domain of the proof of Lemma 6 built on those two points of `D(p,q)`, to
the point `w = g 0`, which lies outside it — and this is impossible by
`AVD.CurveSystem.no_preconnected_crossing`.  Since the points of `G⁺` lying in `D(p,q)`
accumulate at `w`, every common point of `G⁺` and `F⁻` close enough to `w` is of that
kind. -/
theorem exists_branch_disjoint (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hF : BranchBefore f (closure (C.D p r))) (hG : BranchAfter g (closure (C.D p q)))
    (hnd : ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, g x ∉ C.J p q) :
    ∃ δ' > (0 : ℝ), ∃ δ'' > (0 : ℝ), Disjoint (g '' Ioo 0 δ') (f '' Ioo (-δ'') 0) := by
  obtain ⟨hfcont, -, hfrange, -⟩ := hf.1
  have hf0 : f 0 = w := hf.2
  have hg0 : g 0 = w := hg.2
  obtain ⟨δ, hδ, hFsub⟩ := hF
  obtain ⟨δG, hδG, hGsub⟩ := hG
  -- `w` lies on `J(p,r)`, hence in the closure of `D(p,r)`
  have hwcl : w ∈ closure (C.D p r) := by
    rw [closure_D_eq hadm hp hr hpr]
    exact Or.inr (hg.2 ▸ (hg.1.2.2.1 ▸ mem_range_self 0))
  -- the points of `G⁺` in the open half-plane `D(p,q)` accumulate at `w`
  have hnd' : ∀ ε > (0 : ℝ), ∃ x ∈ Ioo (0 : ℝ) ε, g x ∈ C.D p q := by
    intro ε hε
    obtain ⟨x, hx, hxJ⟩ := hnd (min ε δG) (lt_min hε hδG)
    refine ⟨x, ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left ε δG)⟩, ?_⟩
    have hxcl : g x ∈ closure (C.D p q) :=
      hGsub ⟨x, ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right ε δG)⟩, rfl⟩
    rw [closure_D_eq hadm hp hq hpq] at hxcl
    exact hxcl.resolve_right hxJ
  obtain ⟨v, hv, hgv⟩ := hnd' δG hδG
  refine ⟨v, hv.1, δ, hδ, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
  obtain ⟨u, hu, hgu⟩ := hnd' s hs.1
  refine no_preconnected_crossing hadm hp hq hr hpq hqr hpr hg.1 (hu.2.trans hs.2) hgu hgv
    (K := f '' Icc t 0) (isPreconnected_Icc.image f (hfcont.continuousOn)) ?_ ?_
    ⟨hu.2, hs.2⟩ ?_ (Or.inl hu.1) ?_
  · rintro _ ⟨c, -, rfl⟩
    exact hfrange ▸ mem_range_self c
  · rintro _ ⟨c, hc, rfl⟩
    rcases eq_or_lt_of_le hc.2 with h | h
    · rw [h, hf0]; exact hwcl
    · exact hFsub ⟨c, ⟨lt_of_lt_of_le ht.1 hc.1, h⟩, rfl⟩
  · exact ⟨t, ⟨le_refl t, ht.2.le⟩, heq⟩
  · exact ⟨0, ⟨ht.2.le, le_refl 0⟩, by rw [hf0, ← hg0]⟩

/-- A subarc of a globally injective continuous parametrization of a curve is an arc. -/
theorem isArc_subarcParam {γ : ℝ → Plane} (hcont : Continuous γ)
    (hinj : Function.Injective γ) {a b : ℝ} (hab : a < b) : IsArc (subarcParam γ a b) := by
  have hlin : Continuous fun t : ℝ => a + (b - a) * clamp01 t :=
    continuous_const.add (continuous_const.mul continuous_clamp01)
  refine ⟨(hcont.comp hlin).continuousOn, ?_⟩
  intro s hs t ht hst
  have hs' : subarcParam γ a b s = γ (a + (b - a) * s) := by
    change γ (a + (b - a) * clamp01 s) = _
    rw [clamp01_of_mem hs]
  have ht' : subarcParam γ a b t = γ (a + (b - a) * t) := by
    change γ (a + (b - a) * clamp01 t) = _
    rw [clamp01_of_mem ht]
  rw [hs', ht'] at hst
  have := hinj hst
  have hba : 0 < b - a := by linarith
  nlinarith [this]

/-- **The crosscut of Fig. 8(3)** in the proof of **Lemma 8** of
Klein–Langetepe–Nilforoushan (2009).

> Let `H` denote the segment of `U ∩ F⁻` adjacent to `w`; see Fig. 8(3).  Since
> `H ∩ G⁺ ⊆ F⁻ ∩ G⁺ = ∅`, segment `H`, together with parts of `G⁺` and `∂U`, form a simple
> Jordan curve encircling a domain `D`.

This is the first half of that construction: the piece `f([a,0])` of `J(p,q)` ending at `w`
and the piece `g([0,b])` of `J(p,r)` starting at `w` — the two pieces produced by
`AVD.IsProperLineParam.exists_first_exit` and its backward form, so that their endpoints
`f a` and `g b` lie on the frontier of the neighbourhood `U` while the rest of them lies
inside `U` — are joined into a single arc `κ` through `w`.  The hypothesis that the two
pieces meet only at `w` is what `AVD.CurveSystem.exists_branch_disjoint` provides in
configuration BC.  The arc `κ` has both endpoints on `frontier U` and its relative interior
inside `U`: it is a crosscut of `U`, to which the crosscut theorem
`AVD.exists_crosscut_domains` applies. -/
theorem exists_crosscut_arc {f g : ℝ → Plane} {w : Plane} (hfc : Continuous f)
    (hfi : Function.Injective f) (hgc : Continuous g) (hgi : Function.Injective g)
    (hf0 : f 0 = w) (hg0 : g 0 = w) {U : Set Plane} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hfU : f '' Ioc a 0 ⊆ U) (hgU : g '' Ico 0 b ⊆ U)
    (hmeet : f '' Icc a 0 ∩ g '' Icc 0 b ⊆ {w}) :
    ∃ κ : ℝ → Plane, IsArc κ ∧ κ 0 = f a ∧ κ 1 = g b ∧
      κ '' Icc 0 1 = f '' Icc a 0 ∪ g '' Icc 0 b ∧ κ '' Ioo 0 1 ⊆ U ∧ w ∈ κ '' Ioo 0 1 := by
  set γ : ℝ → Plane := subarcParam f a 0 with hγdef
  set δ : ℝ → Plane := subarcParam g 0 b with hδdef
  have hγarc : IsArc γ := isArc_subarcParam hfc hfi ha
  have hδarc : IsArc δ := isArc_subarcParam hgc hgi hb
  have hγ0 : γ 0 = f a := subarcParam_zero f a 0
  have hγ1 : γ 1 = w := by rw [hγdef, subarcParam_one, hf0]
  have hδ0 : δ 0 = w := by rw [hδdef, subarcParam_zero, hg0]
  have hδ1 : δ 1 = g b := subarcParam_one g 0 b
  have hγimg : γ '' Icc 0 1 = f '' Icc a 0 := subarcParam_image ha.le
  have hδimg : δ '' Icc 0 1 = g '' Icc 0 b := subarcParam_image hb.le
  have hmid : γ 1 = δ 0 := by rw [hγ1, hδ0]
  have hint : γ '' Icc 0 1 ∩ δ '' Icc 0 1 ⊆ {γ 1} := by
    rw [hγimg, hδimg, hγ1]
    exact hmeet
  set κ : ℝ → Plane := concatParam γ δ with hκdef
  have hκarc : IsArc κ := hγarc.concat hδarc hmid hint
  have hκ0 : κ 0 = f a := by rw [hκdef, concatParam_zero, hγ0]
  have hκ1 : κ 1 = g b := by rw [hκdef, concatParam_one, hδ1]
  have hκimg : κ '' Icc 0 1 = f '' Icc a 0 ∪ g '' Icc 0 b := by
    rw [hκdef, concatParam_image hmid, hγimg, hδimg]
  refine ⟨κ, hκarc, hκ0, hκ1, hκimg, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxIcc, hxne⟩ := hκarc.image_Ioo_subset_diff hx
    rw [hκimg] at hxIcc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxne
    push Not at hxne
    rcases hxIcc with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · refine hfU ⟨c, ⟨?_, hc.2⟩, rfl⟩
      rcases eq_or_lt_of_le hc.1 with h | h
      · exact absurd (show f c = κ 0 by rw [hκ0, ← h]) hxne.1
      · exact h
    · refine hgU ⟨c, ⟨hc.1, ?_⟩, rfl⟩
      rcases eq_or_lt_of_le hc.2 with h | h
      · exact absurd (show g c = κ 1 by rw [hκ1, h]) hxne.2
      · exact h
  · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [hκdef, concatParam_of_le (le_refl _)]
    norm_num
    exact hγ1

end CurveSystem

end AVD
