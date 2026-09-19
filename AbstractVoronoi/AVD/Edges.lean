import AbstractVoronoi.Paper.Lemma9
import AbstractVoronoi.Jordan.LineComponents

/-!
# The Voronoi edges

The material behind **Theorem 10** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

which is stated and proved in `AbstractVoronoi.Paper.Theorem10`.

Following the proof in the paper, the diagram is decomposed into the finite set `B'` of its
Voronoi vertices (the points lying on at least three region boundaries, finite by Lemma 9)
and the sets `B_{p,q}` of points lying on the boundaries of exactly the two regions of `p`
and `q`; the Voronoi edges are the connected components of `V(S) \ B'`, and each of them is
a connected subset of one bisecting curve `J(p,q)`.  Finiteness of the set of edges comes,
as in the paper, from the fact that the endpoints of the segments of `B_{p,q}` are Voronoi
vertices: on a proper parametrization of `J(p,q)` the set `B_{p,q}` becomes an open subset
of the line whose frontier is finite, and such a set has finitely many components
(`AVD.finite_components_of_finite_frontier`).
-/


noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} (C : CurveSystem S)

/-- The set `B_{p,q}` of the proof of Theorem 10 of Klein–Langetepe–Nilforoushan (2009):

> The rest of `V(S)` is decomposed into sets `B_{p,q}` consisting of all points on the
> boundary of exactly the Voronoi regions `VR(p,S)` and `VR(q,S)`. -/
def BPair (p q : ι) : Set Plane :=
  {z | z ∈ closure (C.VR p S) ∧ z ∈ closure (C.VR q S) ∧
    ∀ r ∈ S, z ∈ closure (C.VR r S) → r = p ∨ r = q}

/-- The open set cutting `B_{p,q}` out of the Voronoi diagram: the complement of the closed
Voronoi regions of the sites other than `p` and `q`. -/
def UPair (p q : ι) : Set Plane := (⋃ r ∈ (S.erase p).erase q, closure (C.VR r S))ᶜ

variable {C}

/-- The set `U_{p,q}` cutting `B_{p,q}` out of the Voronoi diagram is open. -/
theorem UPair_isOpen (p q : ι) : IsOpen (C.UPair p q) :=
  (Set.Finite.isClosed_biUnion ((S.erase p).erase q).finite_toSet
    fun _ _ => isClosed_closure).isOpen_compl

/-- The set `B_{p,q}` of the proof of Theorem 10 of Klein–Langetepe–Nilforoushan (2009) is
symmetric in `p` and `q`. -/
theorem BPair_symm (p q : ι) : C.BPair p q = C.BPair q p := by
  ext z
  simp only [BPair, mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun r hr hz => (h3 r hr hz).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun r hr hz => (h3 r hr hz).symm⟩

/-- The set `B_{p,q}` avoids the closed Voronoi regions of all the other sites, i.e. it is
contained in the open set `U_{p,q}`. -/
theorem BPair_subset_UPair {p q : ι} : C.BPair p q ⊆ C.UPair p q := by
  rintro z ⟨-, -, h3⟩ hz
  obtain ⟨r, hr, hzr⟩ := mem_iUnion₂.1 hz
  rcases h3 r (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)) hzr with rfl | rfl
  · exact (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)) rfl
  · exact (Finset.ne_of_mem_erase hr) rfl

/-- Points of the Voronoi diagram lie in the closures of at least two Voronoi regions; this
is **Lemma 3**. -/
theorem exists_two_closures_of_mem_V (hadm : C.Admissible) {z : Plane} (hz : z ∈ C.V S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ z ∈ closure (C.VR p S) ∧ z ∈ closure (C.VR q S) := by
  rw [(lemma3 hadm).2] at hz
  obtain ⟨p, hp, hz⟩ := mem_iUnion₂.1 hz
  obtain ⟨q, hq, hz1, hz2⟩ := mem_iUnion₂.1 hz
  exact ⟨p, hp, q, Finset.mem_of_mem_erase hq, (Finset.ne_of_mem_erase hq).symm, hz1, hz2⟩

/-- A point of the diagram lying in the closures of three different Voronoi regions is a
Voronoi vertex. -/
theorem mem_vertexSet_of_three_closures {z : Plane} (hz : z ∈ C.V S) {p q r : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : z ∈ closure (C.VR p S)) (h2 : z ∈ closure (C.VR q S))
    (h3 : z ∈ closure (C.VR r S)) : z ∈ C.vertexSet S := by
  refine ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, ?_, ?_, ?_⟩
  · rw [(VR_isOpen Subset.rfl hp).frontier_eq]
    exact ⟨h1, notMem_VR_of_mem_V hz hp⟩
  · rw [(VR_isOpen Subset.rfl hq).frontier_eq]
    exact ⟨h2, notMem_VR_of_mem_V hz hq⟩
  · rw [(VR_isOpen Subset.rfl hr).frontier_eq]
    exact ⟨h3, notMem_VR_of_mem_V hz hr⟩

/-- Voronoi vertices belong to the Voronoi diagram. -/
theorem vertexSet_subset_V : C.vertexSet S ⊆ C.V S := by
  rintro z ⟨p, hp, q, hq, -, -, hpq, -, -, hzp, hzq, -⟩
  exact mem_V_of_two_closures hp hq hpq (frontier_subset_closure hzp)
    (frontier_subset_closure hzq)

/-- `B_{p,q}` is exactly the part of the Voronoi diagram inside the open set `U_{p,q}`. -/
theorem BPair_eq_UPair_inter_V (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : C.BPair p q = C.UPair p q ∩ C.V S := by
  apply Subset.antisymm
  · intro z hz
    exact ⟨BPair_subset_UPair hz, mem_V_of_two_closures hp hq hpq hz.1 hz.2.1⟩
  · rintro z ⟨hzU, hzV⟩
    obtain ⟨p', hp', q', hq', hpq', h1, h2⟩ := exists_two_closures_of_mem_V hadm hzV
    -- the two sites must be `p` and `q`
    have hmem : ∀ r ∈ S, z ∈ closure (C.VR r S) → r = p ∨ r = q := by
      intro r hr hzr
      by_contra hcon
      push Not at hcon
      exact hzU (mem_biUnion (Finset.mem_erase.2 ⟨hcon.2,
        Finset.mem_erase.2 ⟨hcon.1, hr⟩⟩) hzr)
    rcases hmem p' hp' h1 with rfl | rfl
    · rcases hmem q' hq' h2 with rfl | rfl
      · exact absurd rfl hpq'
      · exact ⟨h1, h2, hmem⟩
    · rcases hmem q' hq' h2 with rfl | rfl
      · exact ⟨h2, h1, hmem⟩
      · exact absurd rfl hpq'

/-- `B_{p,q}` is contained in the bisecting curve `J(p,q)`:

> Such a set `B_{p,q}`, if non-empty, consists of disjoint segments of the bisecting curve
> `J(p,q)`. -/
theorem BPair_subset_J {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    C.BPair p q ⊆ C.J p q := by
  rintro z ⟨h1, h2, -⟩
  refine mem_J_of_notMem hp hq hpq ?_ ?_
  · -- `z` is a limit of points of `VR(q,S) ⊆ D(q,p)`, hence not in the open set `D(p,q)`
    intro hzD
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 h2 (C.D p q) (C.D_isOpen p hp q hq hpq) hzD
    exact (Set.disjoint_left.1 (C.D_disjoint p hp q hq hpq)) hy1
      (VR_subset_D (Finset.mem_erase.2 ⟨hpq, hp⟩) hy2)
  · intro hzD
    obtain ⟨y, hy1, hy2⟩ :=
      mem_closure_iff.1 h1 (C.D q p) (C.D_isOpen q hq p hp hpq.symm) hzD
    exact (Set.disjoint_left.1 (C.D_disjoint p hp q hq hpq))
      (VR_subset_D (Finset.mem_erase.2 ⟨hpq.symm, hq⟩) hy2) hy1

/-- Two sets `B_{p,q}` and `B_{p',q'}` are disjoint unless `{p,q} = {p',q'}`, in which case
they are equal. -/
theorem BPair_eq_of_mem_inter {p q p' q' : ι} (hp' : p' ∈ S) (hq' : q' ∈ S)
    (hpq' : p' ≠ q') {z : Plane} (hz : z ∈ C.BPair p q) (hz' : z ∈ C.BPair p' q') :
    C.BPair p q = C.BPair p' q' := by
  obtain ⟨-, -, h3⟩ := hz
  obtain ⟨h1', h2', -⟩ := hz'
  rcases h3 p' hp' h1' with h | h <;> rcases h3 q' hq' h2' with h' | h'
  · exact absurd (h.trans h'.symm) hpq'
  · rw [h, h']
  · rw [h, h']
    exact BPair_symm p q
  · exact absurd (h.trans h'.symm) hpq'

/-- `B_{p,q}` is the part of the bisecting curve `J(p,q)` lying outside the closed Voronoi
regions of the other sites. -/
theorem BPair_eq_UPair_inter_J (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : C.BPair p q = C.UPair p q ∩ C.J p q := by
  apply Subset.antisymm
  · exact fun z hz => ⟨BPair_subset_UPair hz, BPair_subset_J hp hq hpq hz⟩
  · rintro z ⟨hzU, hzJ⟩
    rw [BPair_eq_UPair_inter_V hadm hp hq hpq]
    refine ⟨hzU, ?_⟩
    intro hmem
    obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hmem
    rcases eq_or_ne s p with rfl | hsp
    · exact (notMem_D_of_mem_J hp hq hpq hzJ).1
        (VR_subset_D (Finset.mem_erase.2 ⟨hpq.symm, hq⟩) hzs)
    · rcases eq_or_ne s q with rfl | hsq
      · exact (notMem_D_of_mem_J hp hq hpq hzJ).2
          (VR_subset_D (Finset.mem_erase.2 ⟨hpq, hp⟩) hzs)
      · exact hzU (mem_biUnion (Finset.mem_erase.2 ⟨hsq, Finset.mem_erase.2 ⟨hsp, hs⟩⟩)
          (subset_closure hzs))

/-- Every point of the Voronoi diagram which is not a Voronoi vertex lies in some
`B_{p,q}`. -/
theorem exists_BPair_of_mem_V_diff (hadm : C.Admissible) {z : Plane}
    (hz : z ∈ C.V S \ C.vertexSet S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ z ∈ C.BPair p q := by
  obtain ⟨p, hp, q, hq, hpq, h1, h2⟩ := exists_two_closures_of_mem_V hadm hz.1
  refine ⟨p, hp, q, hq, hpq, h1, h2, ?_⟩
  intro r hr hzr
  by_contra hcon
  push Not at hcon
  exact hz.2 (mem_vertexSet_of_three_closures hz.1 hp hq hr hpq (Ne.symm hcon.1)
    (Ne.symm hcon.2) h1 h2 hzr)

/-- **Each Voronoi edge lies on a single bisecting curve.**  A connected component of
`V(S) \ B'` is contained in one of the sets `B_{p,q}`; this is the step of the proof of
Theorem 10 of Klein–Langetepe–Nilforoushan (2009) where the diagram, minus its vertices, is
decomposed into the sets `B_{p,q}`. -/
theorem connectedComponentIn_subset_BPair (hadm : C.Admissible) {z : Plane}
    (hz : z ∈ C.V S \ C.vertexSet S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      connectedComponentIn (C.V S \ C.vertexSet S) z ⊆ C.BPair p q := by
  classical
  obtain ⟨p, hp, q, hq, hpq, hzB⟩ := exists_BPair_of_mem_V_diff hadm hz
  refine ⟨p, hp, q, hq, hpq, ?_⟩
  set Y : Set Plane := C.V S \ C.vertexSet S with hYdef
  set e : Set Plane := connectedComponentIn Y z with hedef
  set A : Set Plane := C.UPair p q with hAdef
  set B : Set Plane :=
    ⋃ p' ∈ S, ⋃ q' ∈ S.erase p', ⋃ (_ : C.BPair p' q' ∩ C.BPair p q = ∅), C.UPair p' q'
    with hBdef
  have hAopen : IsOpen A := UPair_isOpen p q
  have hBopen : IsOpen B := by
    refine isOpen_biUnion fun p' _ => isOpen_biUnion fun q' _ => ?_
    exact isOpen_iUnion fun _ => UPair_isOpen p' q'
  -- a point of `Y` in `A` lies in `B_{p,q}`
  have hAY : ∀ x ∈ A, x ∈ Y → x ∈ C.BPair p q := by
    intro x hxA hxY
    rw [BPair_eq_UPair_inter_V hadm hp hq hpq]
    exact ⟨hxA, hxY.1⟩
  -- a point of `Y` in `B` lies in a set `B_{p',q'}` disjoint from `B_{p,q}`
  have hBY : ∀ x ∈ B, x ∈ Y → x ∉ C.BPair p q := by
    intro x hxB hxY hxpq
    obtain ⟨p', hp', hx⟩ := mem_iUnion₂.1 hxB
    obtain ⟨q', hq', hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨hdisj, hxU⟩ := mem_iUnion.1 hx
    have hq'S : q' ∈ S := Finset.mem_of_mem_erase hq'
    have hpq'' : p' ≠ q' := (Finset.ne_of_mem_erase hq').symm
    have : x ∈ C.BPair p' q' := by
      rw [BPair_eq_UPair_inter_V hadm hp' hq'S hpq'']
      exact ⟨hxU, hxY.1⟩
    have : x ∈ C.BPair p' q' ∩ C.BPair p q := ⟨this, hxpq⟩
    rw [hdisj] at this
    exact this
  -- every point of `Y` lies in `A` or in `B`
  have hcover : Y ⊆ A ∪ B := by
    intro x hxY
    by_cases hxpq : x ∈ C.BPair p q
    · exact Or.inl (BPair_subset_UPair hxpq)
    · obtain ⟨p', hp', q', hq', hpq'', hxB'⟩ := exists_BPair_of_mem_V_diff hadm hxY
      have hdisj : C.BPair p' q' ∩ C.BPair p q = ∅ := by
        by_contra hne
        obtain ⟨y, hy1, hy2⟩ := Set.nonempty_iff_ne_empty.2 hne
        have := BPair_eq_of_mem_inter hp' hq' hpq'' hy2 hy1
        exact hxpq (by rw [this]; exact hxB')
      refine Or.inr (mem_biUnion hp' (mem_biUnion (Finset.mem_erase.2 ⟨hpq''.symm, hq'⟩)
        (mem_iUnion.2 ⟨hdisj, BPair_subset_UPair hxB'⟩)))
  -- the component is connected, hence stays inside `A`
  by_contra hnot
  obtain ⟨x, hxe, hxpq⟩ := Set.not_subset.1 hnot
  have hxY : x ∈ Y := connectedComponentIn_subset Y z hxe
  have hxAB := hcover hxY
  have hxB : x ∈ B := by
    rcases hxAB with hxA | hxB
    · exact absurd (hAY x hxA hxY) hxpq
    · exact hxB
  have hze : z ∈ e := mem_connectedComponentIn hz
  obtain ⟨y, hye, hyA, hyB⟩ :=
    isPreconnected_connectedComponentIn (x := z) (F := Y) A B hAopen hBopen
      ((connectedComponentIn_subset Y z).trans hcover) ⟨z, hze, BPair_subset_UPair hzB⟩
      ⟨x, hxe, hxB⟩
  exact hBY y hyB (connectedComponentIn_subset Y z hye) (hAY y hyA
    (connectedComponentIn_subset Y z hye))

/-- `B_{p,q}` consists of points of the diagram that are not Voronoi vertices. -/
theorem BPair_subset_V_diff_vertexSet (hadm : C.Admissible) {p q : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hpq : p ≠ q) : C.BPair p q ⊆ C.V S \ C.vertexSet S := by
  intro z hz
  refine ⟨(BPair_eq_UPair_inter_V hadm hp hq hpq ▸ hz).2, ?_⟩
  rintro ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, h₁₂, h₁₃, h₂₃, hz₁, hz₂, hz₃⟩
  have hmem : ∀ r ∈ S, z ∈ frontier (C.VR r S) → r = p ∨ r = q := fun r hr hzr =>
    hz.2.2 r hr (frontier_subset_closure hzr)
  rcases hmem p₁ hp₁ hz₁ with h1 | h1 <;> rcases hmem p₂ hp₂ hz₂ with h2 | h2 <;>
    rcases hmem p₃ hp₃ hz₃ with h3 | h3
  · exact h₁₂ (h1.trans h2.symm)
  · exact h₁₂ (h1.trans h2.symm)
  · exact h₁₃ (h1.trans h3.symm)
  · exact h₂₃ (h2.trans h3.symm)
  · exact h₂₃ (h2.trans h3.symm)
  · exact h₁₃ (h1.trans h3.symm)
  · exact h₁₂ (h1.trans h2.symm)
  · exact h₁₂ (h1.trans h2.symm)

/-- The set of Voronoi vertices of `V(S)` is finite; this is **Lemma 9**. -/
theorem vertexSet_finite (hadm : C.Admissible) : (C.vertexSet S).Finite := by
  have hsub : C.vertexSet S ⊆ ⋃ T ∈ S.powersetCard 3, C.vertexSet T := by
    intro z hz
    obtain ⟨T, hTS, hTcard, hzT⟩ := exists_triple_of_onBoundaryOfThree Subset.rfl hz
    exact mem_biUnion (Finset.mem_powersetCard.2 ⟨hTS, hTcard⟩) hzT
  refine Set.Finite.subset (Set.Finite.biUnion (S.powersetCard 3).finite_toSet ?_) hsub
  intro T hT
  obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.1 hT
  exact (lemma9_three_sites hadm hTS hTcard).1

/-- On a proper parametrization `g` of the bisecting curve `J(p,q)`, the frontier of the
preimage of `U_{p,q}` consists of Voronoi vertices.

This is the step

> Since `J(p,q)` is simple, at most two segments `e` of `B_{p,q}` can share a point of `B'`

of the proof of **Theorem 10** of Klein–Langetepe–Nilforoushan (2009), read on the
parametrizing line: the endpoints of the segments of `B_{p,q}` are Voronoi vertices. -/
theorem frontier_preimage_UPair_subset (hadm : C.Admissible) {p q : ι} (hp : p ∈ S)
    (hq : q ∈ S) (hpq : p ≠ q) {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p q)) :
    frontier (g ⁻¹' (C.UPair p q)) ⊆ g ⁻¹' (C.vertexSet S) := by
  obtain ⟨hcont, hginj, hgrange, -⟩ := hg
  set X : Set ℝ := g ⁻¹' (C.UPair p q) with hXdef
  have hXopen : IsOpen X := (UPair_isOpen p q).preimage hcont
  have hgX : g '' X = C.BPair p q := by
    rw [hXdef, Set.image_preimage_eq_inter_range, hgrange,
      ← BPair_eq_UPair_inter_J hadm hp hq hpq]
  intro t ht
  have htcl : t ∈ closure X := ht.1
  have htnot : t ∉ X := by
    have h := ht.2
    rwa [hXopen.interior_eq] at h
  have hgcl : g t ∈ closure (C.BPair p q) := by
    rw [← hgX]
    exact image_closure_subset_closure_image hcont ⟨t, htcl, rfl⟩
  have hclp : g t ∈ closure (C.VR p S) := by
    have h := closure_mono (fun x (hx : x ∈ C.BPair p q) => hx.1) hgcl
    rwa [closure_closure] at h
  have hclq : g t ∈ closure (C.VR q S) := by
    have h := closure_mono (fun x (hx : x ∈ C.BPair p q) => hx.2.1) hgcl
    rwa [closure_closure] at h
  have hunion : g t ∈ ⋃ r ∈ (S.erase p).erase q, closure (C.VR r S) := by
    by_contra hcon
    exact htnot hcon
  obtain ⟨r, hr, hgr⟩ := mem_iUnion₂.1 hunion
  have hrq : r ≠ q := Finset.ne_of_mem_erase hr
  have hrp : r ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hr)
  have hrS : r ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hr)
  have hVS : g t ∈ C.V S := by
    intro hmem
    obtain ⟨s, hs, hgs⟩ := mem_iUnion₂.1 hmem
    rcases eq_or_ne s p with rfl | hsp
    · exact notMem_VR_of_mem_closure hs hq hpq hclq hgs
    · exact notMem_VR_of_mem_closure hs hp hsp hclp hgs
  exact mem_vertexSet_of_three_closures hVS hp hq hrS hpq (Ne.symm hrp) (Ne.symm hrq)
    hclp hclq hgr

/-- A Voronoi edge lying in `B_{p,q}` is, on a proper parametrization `g` of `J(p,q)`, the
image of a connected component of the open set `g ⁻¹' U_{p,q}`. -/
theorem preimage_edge_eq_component (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p q)) {z : Plane}
    (hz : z ∈ C.V S \ C.vertexSet S)
    (hsub : connectedComponentIn (C.V S \ C.vertexSet S) z ⊆ C.BPair p q)
    {t₀ : ℝ} (ht₀ : g t₀ = z) :
    g ⁻¹' (connectedComponentIn (C.V S \ C.vertexSet S) z)
      = connectedComponentIn (g ⁻¹' (C.UPair p q)) t₀ := by
  obtain ⟨hcont, hginj, hgrange, hgproper⟩ := hg
  have hproperMap : IsProperMap g := isProperMap_iff_isCompact_preimage.2 ⟨hcont, hgproper⟩
  have hind : Topology.IsInducing g :=
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hginj
      hproperMap.isClosedMap).isInducing
  set Y : Set Plane := C.V S \ C.vertexSet S with hYdef
  set X : Set ℝ := g ⁻¹' (C.UPair p q) with hXdef
  have hgX : g '' X = C.BPair p q := by
    rw [hXdef, Set.image_preimage_eq_inter_range, hgrange,
      ← BPair_eq_UPair_inter_J hadm hp hq hpq]
  have hBrange : C.BPair p q ⊆ range g := by
    rw [hgrange]; exact BPair_subset_J hp hq hpq
  have hBY : C.BPair p q ⊆ Y := BPair_subset_V_diff_vertexSet hadm hp hq hpq
  have hze : z ∈ connectedComponentIn Y z := mem_connectedComponentIn hz
  have hgt₀ : g t₀ ∈ C.BPair p q := by rw [ht₀]; exact hsub hze
  have ht₀X : t₀ ∈ X := BPair_subset_UPair hgt₀
  have hsubrange : connectedComponentIn Y z ⊆ range g := hsub.trans hBrange
  apply Subset.antisymm
  · have hpre : IsPreconnected (g ⁻¹' connectedComponentIn Y z) := by
      rw [← hind.isPreconnected_image, Set.image_preimage_eq_of_subset hsubrange]
      exact isPreconnected_connectedComponentIn
    refine hpre.subset_connectedComponentIn (show g t₀ ∈ _ by rw [ht₀]; exact hze) ?_
    intro t ht
    have hgt : g t ∈ C.BPair p q := hsub ht
    rw [← hgX] at hgt
    obtain ⟨t', ht'X, ht'⟩ := hgt
    rwa [← hginj ht']
  · intro t ht
    have himg : g '' connectedComponentIn X t₀ ⊆ connectedComponentIn Y z := by
      refine IsPreconnected.subset_connectedComponentIn
        (isPreconnected_connectedComponentIn.image g hcont.continuousOn) ?_ ?_
      · exact ⟨t₀, mem_connectedComponentIn ht₀X, ht₀⟩
      · refine Subset.trans (image_mono (connectedComponentIn_subset X t₀)) ?_
        rw [hgX]
        exact hBY
    exact himg ⟨t, ht, rfl⟩

/-- **The Voronoi edges lying on one bisecting curve are finite in number.**

> Since `J(p,q)` is simple, at most two segments `e` of `B_{p,q}` can share a point of `B'`.
> Thus, the number of these segments is finite.

On a proper parametrization `g` of `J(p,q)` — which exists by axiom `A₁` — the set
`B_{p,q}` is the image of an open subset `X` of the line whose frontier consists of Voronoi
vertices; by Lemma 9 that frontier is finite, so `X` has finitely many connected components
(`AVD.finite_components_of_finite_frontier`), and the Voronoi edges inside `B_{p,q}` are
their images. -/
theorem finite_edges_in_BPair (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) : {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q}.Finite := by
  classical
  obtain ⟨g, hg⟩ := (hadm.A1 p hp q hq hpq).exists_properParam
  obtain ⟨hcont, hginj, hgrange, -⟩ := id hg
  set X : Set ℝ := g ⁻¹' (C.UPair p q) with hXdef
  have hXopen : IsOpen X := (UPair_isOpen p q).preimage hcont
  have hBrange : C.BPair p q ⊆ range g := by
    rw [hgrange]; exact BPair_subset_J hp hq hpq
  have hfinF : (frontier X).Finite :=
    Set.Finite.subset (Set.Finite.preimage hginj.injOn (vertexSet_finite hadm))
      (frontier_preimage_UPair_subset hadm hp hq hpq hg)
  have hcomps := finite_components_of_finite_frontier hXopen hfinF
  -- each edge inside `B_{p,q}` is the image of a component of `X`
  refine Set.Finite.of_finite_image (f := fun e : Set Plane => g ⁻¹' e)
    (Set.Finite.subset hcomps ?_) ?_
  · rintro I ⟨e, ⟨⟨z₀, hz₀, rfl⟩, hsub⟩, rfl⟩
    have hz₀e : z₀ ∈ connectedComponentIn (C.V S \ C.vertexSet S) z₀ :=
      mem_connectedComponentIn hz₀
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, g t₀ = z₀ := hBrange (hsub hz₀e)
    have hgt₀ : g t₀ ∈ C.BPair p q := by rw [ht₀]; exact hsub hz₀e
    exact ⟨t₀, BPair_subset_UPair hgt₀,
      preimage_edge_eq_component hadm hp hq hpq hg hz₀ hsub ht₀⟩
  · rintro e ⟨-, hsub⟩ e' ⟨-, hsub'⟩ hee'
    have hee'' : g ⁻¹' e = g ⁻¹' e' := hee'
    have h1 : g '' (g ⁻¹' e) = e := Set.image_preimage_eq_of_subset (hsub.trans hBrange)
    have h2 : g '' (g ⁻¹' e') = e' := Set.image_preimage_eq_of_subset (hsub'.trans hBrange)
    rw [← h1, ← h2, hee'']

/-- **Each Voronoi edge is an open subarc of a bisecting curve, and its ends are Voronoi
vertices.**

An edge is a connected component of `V(S)` minus the Voronoi vertices; it lies in one set
`B_{p,q}`, hence on the curve `J(p,q)`, and on a proper parametrization `g` of that curve it
is the image of a connected component `I` of an open subset of the line, the ends of `I`
being frontier points of that set, that is, Voronoi vertices.

This is what makes the Voronoi diagram a plane graph in the sense of
`AVD.IsFinitePlaneGraph`, as used in the proof of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009). -/
theorem edge_isSubarc_and_ends (hadm : C.Admissible) {e : Set Plane} (he : e ∈ C.edgeSet) :
    (∃ (γ : ℝ → Plane) (L : Set Plane) (I : Set ℝ),
        IsProperLineParam γ L ∧ IsOpen I ∧ IsPreconnected I ∧ e = γ '' I) ∧
      closure e \ e ⊆ C.vertexSet S := by
  obtain ⟨z, hz, rfl⟩ := he
  obtain ⟨p, hp, q, hq, hpq, hsub⟩ := connectedComponentIn_subset_BPair hadm hz
  obtain ⟨g, hg⟩ := (hadm.A1 p hp q hq hpq).exists_properParam
  obtain ⟨hcont, hginj, hgrange, hgproper⟩ := id hg
  have hproperMap : IsProperMap g := isProperMap_iff_isCompact_preimage.2 ⟨hcont, hgproper⟩
  have hclosedMap : IsClosedMap g := hproperMap.isClosedMap
  set X : Set ℝ := g ⁻¹' (C.UPair p q) with hXdef
  have hXopen : IsOpen X := (UPair_isOpen p q).preimage hcont
  have hBrange : C.BPair p q ⊆ range g := by
    rw [hgrange]; exact BPair_subset_J hp hq hpq
  set e : Set Plane := connectedComponentIn (C.V S \ C.vertexSet S) z with hedef
  have hze : z ∈ e := mem_connectedComponentIn hz
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, g t₀ = z := hBrange (hsub hze)
  have hgt₀ : g t₀ ∈ C.BPair p q := by rw [ht₀]; exact hsub hze
  have ht₀X : t₀ ∈ X := BPair_subset_UPair hgt₀
  have hIeq : g ⁻¹' e = connectedComponentIn X t₀ :=
    preimage_edge_eq_component hadm hp hq hpq hg hz hsub ht₀
  set I : Set ℝ := connectedComponentIn X t₀ with hIdef
  have hIopen : IsOpen I := hXopen.connectedComponentIn
  have heI : e = g '' I := by
    rw [← hIeq, Set.image_preimage_eq_of_subset (hsub.trans hBrange)]
  refine ⟨⟨g, C.J p q, I, hg, hIopen, isPreconnected_connectedComponentIn, heI⟩, ?_⟩
  -- the closure of the edge is the image of the closure of `I`
  have hclosure : closure e = g '' closure I := by
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal ?_ (hclosedMap _ isClosed_closure)
      rw [heI]
      exact image_mono subset_closure
    · rw [heI]
      exact image_closure_subset_closure_image hcont
  have hdiff : closure e \ e = g '' (closure I \ I) := by
    rw [hclosure, heI, Set.image_sdiff hginj]
  rw [hdiff]
  calc g '' (closure I \ I) ⊆ g '' (frontier X) :=
        image_mono (closure_connectedComponentIn_diff_subset_frontier hXopen ht₀X)
    _ ⊆ g '' (g ⁻¹' (C.vertexSet S)) :=
        image_mono (frontier_preimage_UPair_subset hadm hp hq hpq hg)
    _ ⊆ C.vertexSet S := Set.image_preimage_subset _ _

/-- The set of Voronoi edges of `V(S)` is finite. -/
theorem edgeSet_finite (hadm : C.Admissible) : C.edgeSet.Finite := by
  classical
  have hsub : C.edgeSet ⊆
      ⋃ p ∈ S, ⋃ q ∈ S.erase p, {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q} := by
    rintro e ⟨z, hz, rfl⟩
    obtain ⟨p, hp, q, hq, hpq, hsube⟩ := connectedComponentIn_subset_BPair hadm hz
    exact mem_biUnion hp (mem_biUnion (Finset.mem_erase.2 ⟨hpq.symm, hq⟩)
      ⟨⟨z, hz, rfl⟩, hsube⟩)
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun p hp => ?_) hsub
  refine Set.Finite.biUnion (S.erase p).finite_toSet fun q hq => ?_
  exact finite_edges_in_BPair hadm hp (Finset.mem_of_mem_erase hq)
    (Finset.ne_of_mem_erase hq).symm

/-- The number of Voronoi vertices of `V(S)` is at most `2·C(n,3)`, by **Lemma 9**. -/
theorem vertexSet_ncard_le (hadm : C.Admissible) :
    (C.vertexSet S).ncard ≤ 2 * S.card.choose 3 := by
  classical
  have hsub : C.vertexSet S ⊆ ⋃ T ∈ S.powersetCard 3, C.vertexSet T := by
    intro z hz
    obtain ⟨T, hTS, hTcard, hzT⟩ := exists_triple_of_onBoundaryOfThree Subset.rfl hz
    exact mem_biUnion (Finset.mem_powersetCard.2 ⟨hTS, hTcard⟩) hzT
  have hfin : ∀ T ∈ S.powersetCard 3, (C.vertexSet T).Finite := by
    intro T hT
    obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.1 hT
    exact (lemma9_three_sites hadm hTS hTcard).1
  have hbig : (⋃ T ∈ S.powersetCard 3, C.vertexSet T).Finite :=
    Set.Finite.biUnion (S.powersetCard 3).finite_toSet hfin
  calc (C.vertexSet S).ncard ≤ (⋃ T ∈ S.powersetCard 3, C.vertexSet T).ncard :=
        Set.ncard_le_ncard hsub hbig
    _ ≤ ∑ T ∈ S.powersetCard 3, (C.vertexSet T).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _T ∈ S.powersetCard 3, 2 := by
        refine Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.1 hT
        exact (lemma9_three_sites hadm hTS hTcard).2
    _ = 2 * S.card.choose 3 := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, Nat.mul_comm]

/-- **The quantitative form of `AVD.CurveSystem.finite_edges_in_BPair`**: the Voronoi edges
lying on one bisecting curve are at most one more in number than there are Voronoi vertices,
hence at most `2·C(n,3) + 1` by Lemma 9.

On a proper parametrization of `J(p,q)` the edges inside `B_{p,q}` are the images of the
connected components of an open subset of the line whose frontier consists of Voronoi
vertices, and an open subset of the line has at most one more component than it has frontier
points (`AVD.ncard_components_le_frontier`). -/
theorem ncard_edges_in_BPair_le (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) :
    {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q}.ncard ≤ 2 * S.card.choose 3 + 1 := by
  classical
  obtain ⟨g, hg⟩ := (hadm.A1 p hp q hq hpq).exists_properParam
  obtain ⟨hcont, hginj, hgrange, -⟩ := id hg
  set X : Set ℝ := g ⁻¹' (C.UPair p q) with hXdef
  have hXopen : IsOpen X := (UPair_isOpen p q).preimage hcont
  have hBrange : C.BPair p q ⊆ range g := by
    rw [hgrange]; exact BPair_subset_J hp hq hpq
  have hfront : frontier X ⊆ g ⁻¹' (C.vertexSet S) :=
    frontier_preimage_UPair_subset hadm hp hq hpq hg
  have hfinF : (frontier X).Finite :=
    Set.Finite.subset (Set.Finite.preimage hginj.injOn (vertexSet_finite hadm)) hfront
  -- there are at most as many frontier points as Voronoi vertices
  have hfrontcard : (frontier X).ncard ≤ 2 * S.card.choose 3 := by
    refine le_trans (Set.ncard_le_ncard_of_injOn g (fun t ht => hfront ht) hginj.injOn
      (vertexSet_finite hadm)) ?_
    exact vertexSet_ncard_le hadm
  -- the edges inside `B_{p,q}` inject into the components of `X`
  have hmaps : ∀ e ∈ {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q},
      g ⁻¹' e ∈ {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x} := by
    rintro e ⟨⟨z₀, hz₀, rfl⟩, hsub⟩
    have hz₀e : z₀ ∈ connectedComponentIn (C.V S \ C.vertexSet S) z₀ :=
      mem_connectedComponentIn hz₀
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, g t₀ = z₀ := hBrange (hsub hz₀e)
    have hgt₀ : g t₀ ∈ C.BPair p q := by rw [ht₀]; exact hsub hz₀e
    exact ⟨t₀, BPair_subset_UPair hgt₀,
      preimage_edge_eq_component hadm hp hq hpq hg hz₀ hsub ht₀⟩
  have hinj : Set.InjOn (fun e : Set Plane => g ⁻¹' e)
      {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q} := by
    rintro e ⟨-, hsub⟩ e' ⟨-, hsub'⟩ hee'
    have hee'' : g ⁻¹' e = g ⁻¹' e' := hee'
    have h1 : g '' (g ⁻¹' e) = e := Set.image_preimage_eq_of_subset (hsub.trans hBrange)
    have h2 : g '' (g ⁻¹' e') = e' := Set.image_preimage_eq_of_subset (hsub'.trans hBrange)
    rw [← h1, ← h2, hee'']
  calc {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q}.ncard
      ≤ {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x}.ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
          (finite_components_of_finite_frontier hXopen hfinF)
    _ ≤ (frontier X).ncard + 1 := ncard_components_le_frontier hXopen hfinF
    _ ≤ 2 * S.card.choose 3 + 1 := Nat.add_le_add_right hfrontcard 1


/-- **An explicit bound on the number of Voronoi edges**, with no appeal to Euler's formula:
every edge lies in one of the `C(n,2)` sets `B_{p,q}`, and each of those contains at most
`2·C(n,3) + 1` edges (`AVD.CurveSystem.ncard_edges_in_BPair_le`).

This is the quantitative form of `AVD.CurveSystem.edgeSet_finite`.  It is polynomial, not
linear, and so is weaker than the count `O(n)` of Theorem 10, which needs Euler's formula
(see `AVD.EulerSphereInput`); but unlike that count it is proved. -/
theorem edgeSet_ncard_le (hadm : C.Admissible) :
    C.edgeSet.ncard ≤ S.card.choose 2 * (2 * S.card.choose 3 + 1) := by
  classical
  -- the edges lying on the bisecting curve of an unordered pair of sites
  set E : Finset ι → Set (Set Plane) := fun T =>
    {e : Set Plane | e ∈ C.edgeSet ∧ ∃ p ∈ T, ∃ q ∈ T, p ≠ q ∧ e ⊆ C.BPair p q}
  -- for a pair `T = {p, q}` these are exactly the edges inside `B_{p,q}`
  have hpair : ∀ T ∈ S.powersetCard 2,
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ E T ⊆ {e : Set Plane | e ∈ C.edgeSet ∧ e ⊆ C.BPair p q} := by
    intro T hT
    obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.1 hT
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.1 hTcard
    have hp : p ∈ S := hTS (by simp)
    have hq : q ∈ S := hTS (by simp)
    refine ⟨p, hp, q, hq, hpq, ?_⟩
    rintro e ⟨he, p', hp', q', hq', hp'q', hsub⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp' hq'
    refine ⟨he, ?_⟩
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
    · exact absurd rfl hp'q'
    · exact hsub
    · rw [BPair_symm] at hsub; exact hsub
    · exact absurd rfl hp'q'
  have hEfin : ∀ T ∈ S.powersetCard 2, (E T).Finite := by
    intro T hT
    obtain ⟨p, hp, q, hq, hpq, hsub⟩ := hpair T hT
    exact (finite_edges_in_BPair hadm hp hq hpq).subset hsub
  have hEcard : ∀ T ∈ S.powersetCard 2, (E T).ncard ≤ 2 * S.card.choose 3 + 1 := by
    intro T hT
    obtain ⟨p, hp, q, hq, hpq, hsub⟩ := hpair T hT
    exact le_trans (Set.ncard_le_ncard hsub (finite_edges_in_BPair hadm hp hq hpq))
      (ncard_edges_in_BPair_le hadm hp hq hpq)
  have hsub : C.edgeSet ⊆ ⋃ T ∈ S.powersetCard 2, E T := by
    rintro e ⟨z, hz, rfl⟩
    obtain ⟨p, hp, q, hq, hpq, hsube⟩ := connectedComponentIn_subset_BPair hadm hz
    have hTmem : ({p, q} : Finset ι) ∈ S.powersetCard 2 :=
      Finset.mem_powersetCard.2
        ⟨by simp [Finset.insert_subset_iff, hp, hq], Finset.card_pair hpq⟩
    exact mem_biUnion hTmem ⟨⟨z, hz, rfl⟩, p, by simp, q, by simp, hpq, hsube⟩
  have hfin : (⋃ T ∈ S.powersetCard 2, E T).Finite :=
    Set.Finite.biUnion (S.powersetCard 2).finite_toSet hEfin
  calc C.edgeSet.ncard ≤ (⋃ T ∈ S.powersetCard 2, E T).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ ∑ T ∈ S.powersetCard 2, (E T).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _T ∈ S.powersetCard 2, (2 * S.card.choose 3 + 1) := Finset.sum_le_sum hEcard
    _ = S.card.choose 2 * (2 * S.card.choose 3 + 1) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

end CurveSystem

end AVD
