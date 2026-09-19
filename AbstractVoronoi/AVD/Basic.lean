import AbstractVoronoi.Paper.Definitions

/-!
# Curve systems: the basic API

Elementary consequences of the definitions of Section 2 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

which are formalised in `AbstractVoronoi.Paper.Definitions`: the symmetry `J(p,q) = J(q,p)`
(derived, not assumed), openness and disjointness of the Voronoi regions, the description of
the two domains of a bisecting curve through the Jordan curve theorem, and the consequences
of Theorem 4 of the paper that the later proofs use.

The numbered statements themselves are elsewhere: **Definition 1** and **Definition 2** in
`AbstractVoronoi.Paper.Definitions`, **Lemma 3** in `AbstractVoronoi.Paper.Lemma3`, **Lemma 5**
in `AbstractVoronoi.Paper.Lemma5`.

Theorem 4 of the paper is used through `AVD.jordanCurveLocalStructure`
(`AbstractVoronoi.Jordan.LocalStructure`), the form of its local part that the paper actually
uses after Theorem 4; its global part is proved in `AbstractVoronoi.Jordan.Schoenflies` and
`AbstractVoronoi.Jordan.SphereTransfer`.
-/


noncomputable section

open Set Topology

namespace AVD

variable {ι : Type*} [DecidableEq ι]

namespace CurveSystem

variable {S : Finset ι} (C : CurveSystem S)

omit [DecidableEq ι] in
/-- `J(p,q) = J(q,p)`, the symmetry of the bisecting curves required at the beginning of
Section 2 of Klein–Langetepe–Nilforoushan (2009):

> for any two indices `p ≠ q` of `S`, a curve `J(p,q) = J(q,p)` that splits the plane into
> two unbounded domains, labeled `D(p,q)` and `D(q,p)`.

Symmetry is not an independent requirement: since `J(p,q)` is the complement of
`D(p,q) ∪ D(q,p)` and `J(q,p)` is the complement of `D(q,p) ∪ D(p,q)`, the two curves
coincide.  It is therefore *derived* here from the splitting property `compl_J` rather than
imposed as part of the data. -/
theorem J_symm {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) : C.J p q = C.J q p := by
  have h : (C.J p q)ᶜ = (C.J q p)ᶜ := by
    rw [C.compl_J p hp q hq hpq, C.compl_J q hq p hp hpq.symm, union_comm]
  simpa using congrArg compl h

/-! ## Elementary consequences of the definitions -/

variable {C}

/-- The Voronoi region of `p` is contained in each half-plane `D(p,q)` defining it; see
equation (1) of Klein–Langetepe–Nilforoushan (2009). -/
theorem VR_subset_D {p q : ι} {S' : Finset ι} (hq : q ∈ S'.erase p) :
    C.VR p S' ⊆ C.D p q := by
  intro z hz
  exact (mem_iInter₂.1 hz) q hq

/-- Membership in the Voronoi region of `p`, unfolded from equation (1) of
Klein–Langetepe–Nilforoushan (2009). -/
theorem mem_VR_iff {p : ι} {S' : Finset ι} {z : Plane} :
    z ∈ C.VR p S' ↔ ∀ q ∈ S'.erase p, z ∈ C.D p q := mem_iInter₂

/-- Voronoi regions are open, being finite intersections of the open half-planes `D(p,q)`. -/
theorem VR_isOpen {p : ι} {S' : Finset ι} (hS' : S' ⊆ S) (hp : p ∈ S) :
    IsOpen (C.VR p S') := by
  refine isOpen_biInter_finset ?_
  intro q hq
  exact C.D_isOpen p hp q (hS' (Finset.mem_of_mem_erase hq))
    (Ne.symm (Finset.ne_of_mem_erase hq))

/-- Voronoi regions of distinct sites are disjoint. -/
theorem VR_disjoint {p q : ι} {S' : Finset ι} (hS' : S' ⊆ S) (hp : p ∈ S') (hq : q ∈ S')
    (hpq : p ≠ q) : Disjoint (C.VR p S') (C.VR q S') := by
  refine Set.disjoint_left.2 fun z hzp hzq => ?_
  have h1 : z ∈ C.D p q := VR_subset_D (Finset.mem_erase.2 ⟨Ne.symm hpq, hq⟩) hzp
  have h2 : z ∈ C.D q p := VR_subset_D (Finset.mem_erase.2 ⟨hpq, hp⟩) hzq
  exact (Set.disjoint_left.1 (C.D_disjoint p (hS' hp) q (hS' hq) hpq)) h1 h2

/-- A point in the closure of one Voronoi region lies in no other Voronoi region. -/
theorem notMem_VR_of_mem_closure {s t : ι} (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t)
    {z : Plane} (hz : z ∈ closure (C.VR t S)) : z ∉ C.VR s S := by
  intro hmem
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hz (C.VR s S) (VR_isOpen Subset.rfl hs) hmem
  exact (Set.disjoint_left.1 (VR_disjoint Subset.rfl hs ht hst)) hy1 hy2

/-- A point lying in the closures of two different Voronoi regions belongs to the Voronoi
diagram. -/
theorem mem_V_of_two_closures {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane}
    (h1 : z ∈ closure (C.VR p S)) (h2 : z ∈ closure (C.VR q S)) : z ∈ C.V S := by
  intro hmem
  obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hmem
  rcases eq_or_ne s p with rfl | hsp
  · exact notMem_VR_of_mem_closure hs hq hpq h2 hzs
  · exact notMem_VR_of_mem_closure hs hp hsp h1 hzs

/-- A point of the Voronoi diagram lies in no Voronoi region; see equation (2) of
Klein–Langetepe–Nilforoushan (2009). -/
theorem notMem_VR_of_mem_V {z : Plane} (hz : z ∈ C.V S) {t : ι} (ht : t ∈ S) :
    z ∉ C.VR t S := fun h => hz (mem_biUnion ht h)

omit [DecidableEq ι] in
/-- A point of the bisecting curve `J(p,q)` lies in neither of its two half-planes. -/
theorem notMem_D_of_mem_J {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane}
    (hz : z ∈ C.J p q) : z ∉ C.D p q ∧ z ∉ C.D q p := by
  have : z ∉ (C.J p q)ᶜ := by simpa using hz
  rw [C.compl_J p hp q hq hpq] at this
  exact ⟨fun h => this (Or.inl h), fun h => this (Or.inr h)⟩

omit [DecidableEq ι] in
/-- A point lying in neither half-plane of `J(p,q)` lies on the curve `J(p,q)` itself. -/
theorem mem_J_of_notMem {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane}
    (h1 : z ∉ C.D p q) (h2 : z ∉ C.D q p) : z ∈ C.J p q := by
  by_contra h
  have : z ∈ (C.J p q)ᶜ := h
  rw [C.compl_J p hp q hq hpq] at this
  rcases this with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- **The half-planes of a bisecting curve of an admissible system are non-empty.**

The printed definition of a curve system (beginning of Section 2 of
Klein–Langetepe–Nilforoushan (2009)) requires `J(p,q)` to split the plane into two
*unbounded domains*; the formal `AVD.CurveSystem` only requires the two labelled pieces to
be open, disjoint, preconnected and complementary to the curve, and non-emptiness is
recovered here from axiom `A₁`: the curve separates the plane into exactly two domains
`D₁, D₂` (Theorem 4), and if `D(p,q)` were empty, the preconnected set `D(q,p)` would be the
disjoint union of the two non-empty open sets `D₁` and `D₂`. -/
theorem D_nonempty (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    (C.D p q).Nonempty := by
  rcases Set.eq_empty_or_nonempty (C.D p q) with h | h
  · exfalso
    obtain ⟨D₁, D₂, hO1, hO2, hc1, hc2, hd12, hu12, -, -⟩ :=
      (hadm.A1 p hp q hq hpq).exists_separation_frontier_eq
    have hcover : C.D q p = D₁ ∪ D₂ := by
      rw [hu12, C.compl_J p hp q hq hpq, h, empty_union]
    have hpre : IsPreconnected (C.D q p) := C.D_isPreconnected q hq p hp (Ne.symm hpq)
    obtain ⟨x, hx1⟩ := hc1.nonempty
    obtain ⟨y, hy2⟩ := hc2.nonempty
    obtain ⟨z, -, hz1, hz2⟩ := hpre D₁ D₂ hO1 hO2 hcover.subset
      ⟨x, by rw [hcover]; exact Or.inl hx1, hx1⟩ ⟨y, by rw [hcover]; exact Or.inr hy2, hy2⟩
    exact (Set.disjoint_left.1 hd12) hz1 hz2
  · exact h

/-- **The half-planes of a bisecting curve of an admissible system are domains**, i.e.
non-empty and connected, as required at the beginning of Section 2 of
Klein–Langetepe–Nilforoushan (2009).  Connectedness of the two pieces is part of the data of
an `AVD.CurveSystem` only in the weaker, preconnected form; non-emptiness comes from axiom
`A₁` through `AVD.CurveSystem.D_nonempty`. -/
theorem D_isConnected (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : IsConnected (C.D p q) :=
  ⟨D_nonempty hadm hp hq hpq, C.D_isPreconnected p hp q hq hpq⟩

/-- The two complementary domains of a bisecting curve `J(p,q)`, as produced by the Jordan
curve theorem, are exactly `D(p,q)` and `D(q,p)`: every splitting of the complement of
`J(p,q)` into two connected pieces must be that one.  This is the identification step used
whenever Theorem 4 of Klein–Langetepe–Nilforoushan (2009) is applied to a bisecting curve. -/
theorem D_eq_of_separation (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {D₁ D₂ : Set Plane} (hc1 : IsConnected D₁) (hc2 : IsConnected D₂)
    (hu12 : D₁ ∪ D₂ = (C.J p q)ᶜ) : C.D p q = D₁ ∨ C.D p q = D₂ := by
  have hcompl : (C.J p q)ᶜ = C.D p q ∪ C.D q p := C.compl_J p hp q hq hpq
  have hcover : D₁ ∪ D₂ = C.D p q ∪ C.D q p := by rw [hu12, hcompl]
  have hOpq : IsOpen (C.D p q) := C.D_isOpen p hp q hq hpq
  have hOqp : IsOpen (C.D q p) := C.D_isOpen q hq p hp (Ne.symm hpq)
  have hdpq : Disjoint (C.D p q) (C.D q p) := C.D_disjoint p hp q hq hpq
  have h1 : D₁ ⊆ C.D p q ∨ D₁ ⊆ C.D q p :=
    hc1.isPreconnected.subset_or_subset hOpq hOqp hdpq (hcover ▸ subset_union_left)
  have h2 : D₂ ⊆ C.D p q ∨ D₂ ⊆ C.D q p :=
    hc2.isPreconnected.subset_or_subset hOpq hOqp hdpq (hcover ▸ subset_union_right)
  have hne_pq : (C.D p q).Nonempty := D_nonempty hadm hp hq hpq
  have hne_qp : (C.D q p).Nonempty := D_nonempty hadm hq hp (Ne.symm hpq)
  have hsubpq : C.D p q ⊆ D₁ ∪ D₂ := hcover ▸ subset_union_left
  have hsubqp : C.D q p ⊆ D₁ ∪ D₂ := hcover ▸ subset_union_right
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso
    obtain ⟨z, hz⟩ := hne_qp
    rcases hsubqp hz with h | h
    · exact absurd (h1 h) (Set.disjoint_right.1 hdpq hz)
    · exact absurd (h2 h) (Set.disjoint_right.1 hdpq hz)
  · refine Or.inl (Subset.antisymm ?_ h1)
    intro z hz
    rcases hsubpq hz with h | h
    · exact h
    · exact absurd (h2 h) (Set.disjoint_left.1 hdpq hz)
  · refine Or.inr (Subset.antisymm ?_ h2)
    intro z hz
    rcases hsubpq hz with h | h
    · exact absurd (h1 h) (Set.disjoint_left.1 hdpq hz)
    · exact h
  · exfalso
    obtain ⟨z, hz⟩ := hne_pq
    rcases hsubpq hz with h | h
    · exact absurd (h1 h) (Set.disjoint_left.1 hdpq hz)
    · exact absurd (h2 h) (Set.disjoint_left.1 hdpq hz)

/-- The common boundary of the two domains of a bisecting curve is the curve itself.  This
is the first assertion of Theorem 4 of Klein–Langetepe–Nilforoushan (2009), transported to
the bisecting curves `J(p,q)` of an admissible system.

This uses only the *global*, proved part of Theorem 4
(`AVD.IsUnboundedJordanCurve.exists_separation_frontier_eq`), so it carries no assumption. -/
theorem frontier_D_eq_J (hadm : C.Admissible) {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) : frontier (C.D p q) = C.J p q := by
  obtain ⟨D₁, D₂, -, -, hc1, hc2, -, hu12, hf1, hf2⟩ :=
    (hadm.A1 p hp q hq hpq).exists_separation_frontier_eq
  rcases D_eq_of_separation hadm hp hq hpq hc1 hc2 hu12 with h | h
  · rw [h, hf1]
  · rw [h, hf2]

/-- **The half-planes of a bisecting curve of an admissible system are unbounded**, as
required at the beginning of Section 2 of Klein–Langetepe–Nilforoushan (2009).  This is not
part of the data of an `AVD.CurveSystem`: it follows from axiom `A₁`, because the common
boundary of the two half-planes is the curve `J(p,q)` itself, which is unbounded
(`AVD.IsUnboundedJordanCurve.not_isBounded`). -/
theorem D_not_isBounded (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : ¬ Bornology.IsBounded (C.D p q) := by
  intro hbdd
  refine (hadm.A1 p hp q hq hpq).not_isBounded ?_
  rw [← frontier_D_eq_J hadm hp hq hpq]
  exact hbdd.closure.subset frontier_subset_closure

/-- Theorem 4 of Klein–Langetepe–Nilforoushan (2009), specialised to a bisecting curve
`J(p,q)` of an admissible curve system: the two domains provided by Theorem 4 are exactly
`D(p,q)` and `D(q,p)`, so that `J(p,q)` is their common boundary, and every point of
`J(p,q)` is accessible from `D(p,q)` inside arbitrarily small neighbourhoods. -/
theorem exists_theorem4_data (hadm : C.Admissible) {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    frontier (C.D p q) = C.J p q ∧
      ∀ z ∈ C.J p q, ∀ V ∈ 𝓝 z, ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧
        IsConnected (U ∩ C.D p q) ∧
        ∀ x ∈ U ∩ C.D p q, AccessibleWithin (U ∩ C.D p q) x z := by
  refine ⟨frontier_D_eq_J hadm hp hq hpq, ?_⟩
  obtain ⟨D₁, D₂, hO1, hO2, hc1, hc2, hd12, hu12, hf1, hf2⟩ :=
    (hadm.A1 p hp q hq hpq).exists_separation_frontier_eq
  have hacc := jordanCurveLocalStructure (C.J p q) (Or.inr (hadm.A1 p hp q hq hpq))
    D₁ D₂ hO1 hO2 hc1 hc2 hd12 hu12 hf1 hf2
  rcases D_eq_of_separation hadm hp hq hpq hc1 hc2 hu12 with hkey | hkey
  · intro z hz V hV
    obtain ⟨U, hUnhds, hUV, hUopen, hconn, -, haccess, -⟩ := hacc z hz V hV
    exact ⟨U, hUnhds, hUV, hUopen, by rw [hkey]; exact hconn, by rw [hkey]; exact haccess⟩
  · intro z hz V hV
    obtain ⟨U, hUnhds, hUV, hUopen, -, hconn, -, haccess⟩ := hacc z hz V hV
    exact ⟨U, hUnhds, hUV, hUopen, by rw [hkey]; exact hconn, by rw [hkey]; exact haccess⟩

/-- The closure of a domain `D(p,q)` is `D(p,q) ∪ J(p,q)`; a consequence of Theorem 4 of
Klein–Langetepe–Nilforoushan (2009). -/
theorem closure_D_eq (hadm : C.Admissible) {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    closure (C.D p q) = C.D p q ∪ C.J p q := by
  rw [← frontier_D_eq_J hadm hp hq hpq, closure_eq_self_union_frontier]

/-- Every point of a bisecting curve is a limit of points of each of its two domains;
a consequence of Theorem 4 of Klein–Langetepe–Nilforoushan (2009). -/
theorem mem_closure_D_of_mem_J (hadm : C.Admissible)
    {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane} (hz : z ∈ C.J p q) :
    z ∈ closure (C.D p q) := by
  have : z ∈ frontier (C.D p q) := by rw [frontier_D_eq_J hadm hp hq hpq]; exact hz
  exact frontier_subset_closure this

/-- Accessibility of the points of a bisecting curve from its domains, in the form in which
it is used in the paper: a point `z` of `J(p,q)` is accessible from `D(p,q)` by an arc that
can be required to stay inside any prescribed neighbourhood `V` of `z` (the "shortening" of
access arcs in the proof of Lemma 6 of Klein–Langetepe–Nilforoushan (2009)). -/
theorem accessibleFrom_of_mem_J (hadm : C.Admissible) {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) {z : Plane} (hz : z ∈ C.J p q)
    {V : Set Plane} (hV : V ∈ 𝓝 z) : AccessibleFrom (V ∩ C.D p q) z := by
  obtain ⟨-, hacc⟩ := exists_theorem4_data hadm hp hq hpq
  obtain ⟨U, -, hUV, -, hconn, haccess⟩ := hacc z hz V hV
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨γ, harc, -, h1, hsub⟩ := haccess x hx
  exact ⟨γ, harc, h1, hsub.trans (inter_subset_inter_left _ hUV)⟩

/-- The Voronoi region of `a` with respect to the three sites `{a, b, c}` is the
intersection of the two half-planes `D(a,b)` and `D(a,c)`. -/
theorem VR_triple {T : Finset ι} {a b c : ι} (hT : T = {a, b, c}) (hab : a ≠ b) (hac : a ≠ c) :
    C.VR a T = C.D a b ∩ C.D a c := by
  subst hT
  ext z
  simp only [VR, mem_iInter, mem_inter_iff]
  constructor
  · intro h
    exact ⟨h b (by simp [Finset.mem_erase, Ne.symm hab]),
      h c (by simp [Finset.mem_erase, Ne.symm hac])⟩
  · rintro ⟨h1, h2⟩ x hx
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨hxa, hx⟩ := hx
    rcases hx with rfl | rfl | rfl
    · exact absurd rfl hxa
    · exact h1
    · exact h2

/-! ## An auxiliary step for Lemma 5 -/

/-- Auxiliary step in the proof of **Lemma 5** of Klein–Langetepe–Nilforoushan (2009):
no point can lie in `D(p,q) ∩ D(q,r) ∩ D(r,p)`, since the three closed Voronoi regions of
`S' = {p,q,r}` cover the plane by axiom `A₃`. -/
theorem no_mem_cyclic (hadm : C.Admissible) {p q r : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    C.D p q ∩ C.D q r ∩ C.D r p = ∅ := by
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨hz1, hz2⟩ hz3
  set S' : Finset ι := {p, q, r} with hS'def
  have hS' : S' ⊆ S := by
    intro x hx
    simp only [hS'def, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hpS' : p ∈ S' := by simp [hS'def]
  have hqS' : q ∈ S' := by simp [hS'def]
  have hrS' : r ∈ S' := by simp [hS'def]
  have hcover : z ∈ (⋃ s ∈ S', closure (C.VR s S')) := by rw [hadm.A3 S' hS']; trivial
  obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hcover
  simp only [hS'def, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · -- `VR(p, S') ⊆ D(p,r)`, but `z ∈ D(r,p)`
    have hmem : r ∈ S'.erase s := Finset.mem_erase.2 ⟨Ne.symm hpr, hrS'⟩
    have hzcl : z ∈ closure (C.D s r) := closure_mono (fun y hy => VR_subset_D hmem hy) hzs
    rw [closure_D_eq hadm hp hr hpr] at hzcl
    rcases hzcl with h | h
    · exact (Set.disjoint_left.1 (C.D_disjoint s hp r hr hpr)) h hz3
    · exact (notMem_D_of_mem_J hp hr hpr h).2 hz3
  · -- `VR(q, S') ⊆ D(q,p)`, but `z ∈ D(p,q)`
    have hmem : p ∈ S'.erase s := Finset.mem_erase.2 ⟨hpq, hpS'⟩
    have hzcl : z ∈ closure (C.D s p) := closure_mono (fun y hy => VR_subset_D hmem hy) hzs
    rw [closure_D_eq hadm hq hp (Ne.symm hpq)] at hzcl
    rcases hzcl with h | h
    · exact (Set.disjoint_left.1 (C.D_disjoint s hq p hp (Ne.symm hpq))) h hz1
    · exact (notMem_D_of_mem_J hq hp (Ne.symm hpq) h).2 hz1
  · -- `VR(r, S') ⊆ D(r,q)`, but `z ∈ D(q,r)`
    have hmem : q ∈ S'.erase s := Finset.mem_erase.2 ⟨hqr, hqS'⟩
    have hzcl : z ∈ closure (C.D s q) := closure_mono (fun y hy => VR_subset_D hmem hy) hzs
    rw [closure_D_eq hadm hr hq (Ne.symm hqr)] at hzcl
    rcases hzcl with h | h
    · exact (Set.disjoint_left.1 (C.D_disjoint s hr q hq (Ne.symm hqr))) h hz2
    · exact (notMem_D_of_mem_J hr hq (Ne.symm hqr) h).2 hz2

end CurveSystem

end AVD
