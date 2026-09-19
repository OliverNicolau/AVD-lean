import AbstractVoronoi.Paper.Lemma8
import AbstractVoronoi.Jordan.K33

/-!
# Many sites: the Voronoi vertices

Subsection 3.2 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

This file defines the set of Voronoi vertices (the points lying on the boundaries of at
least three Voronoi regions), the set of Voronoi edges, and proves the three-site case of
Lemma 9 by Thomassen's argument through the non-planarity of `K₃,₃`
(`AVD.CurveSystem.lemma9_three_sites`).

**Lemma 9** itself is in `AbstractVoronoi.Paper.Lemma9`.
-/


noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} (C : CurveSystem S)

/-- `z` lies on the boundaries of at least three Voronoi regions of the diagram `V(S')`.
This is the defining property of the set `B` in Lemma 9 of
Klein–Langetepe–Nilforoushan (2009). -/
def OnBoundaryOfThree (S' : Finset ι) (z : Plane) : Prop :=
  ∃ p ∈ S', ∃ q ∈ S', ∃ r ∈ S', p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
    z ∈ frontier (C.VR p S') ∧ z ∈ frontier (C.VR q S') ∧ z ∈ frontier (C.VR r S')

/-- The set of *Voronoi vertices* of the diagram `V(S')`: the points lying on the
boundaries of at least three Voronoi regions of `V(S')`.  This is the set `B'` in the proof
of Theorem 10 of Klein–Langetepe–Nilforoushan (2009). -/
def vertexSet (S' : Finset ι) : Set Plane := {z | C.OnBoundaryOfThree S' z}

/-- The set `B` of Lemma 9 of Klein–Langetepe–Nilforoushan (2009): all points on the
boundaries of at least three Voronoi regions in some Voronoi diagram `V(S')`, `S' ⊆ S`. -/
def BSet : Set Plane := {z | ∃ S' ⊆ S, C.OnBoundaryOfThree S' z}

/-- The *edges* of the Voronoi diagram `V(S)`: the connected components of `V(S)` minus its
set of Voronoi vertices.  Cf. the proof of Theorem 10 of
Klein–Langetepe–Nilforoushan (2009), where the edges are the maximal connected pieces of
the sets `B_{p,q}`. -/
def edgeSet : Set (Set Plane) :=
  {e | ∃ z ∈ C.V S \ C.vertexSet S, e = connectedComponentIn (C.V S \ C.vertexSet S) z}

variable {C}

/-- Voronoi regions can only grow when sites are removed. -/
theorem VR_mono {p : ι} {T S' : Finset ι} (hT : T ⊆ S') : C.VR p S' ⊆ C.VR p T := by
  intro z hz
  refine mem_VR_iff.2 fun q hq => ?_
  exact mem_VR_iff.1 hz q (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hq,
    hT (Finset.mem_of_mem_erase hq)⟩)

/-- Every point on the boundaries of three Voronoi regions of a diagram `V(S')` is a point
on the boundaries of the three corresponding regions of the diagram of just those three
sites.  This is the reduction step in the proof of Lemma 9 of
Klein–Langetepe–Nilforoushan (2009): "Since the Voronoi regions of these indices in `V(S'')`
can only be larger than those in `V(S')`, point `v` belongs to the region boundaries of
`p, q, r` in `V(S'')`, too." -/
theorem exists_triple_of_onBoundaryOfThree {S' : Finset ι} (hS' : S' ⊆ S) {z : Plane}
    (hz : C.OnBoundaryOfThree S' z) :
    ∃ T ⊆ S', T.card = 3 ∧ C.OnBoundaryOfThree T z := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, hzp, hzq, hzr⟩ := hz
  set T : Finset ι := {p, q, r} with hTdef
  have hpT : p ∈ T := by simp [hTdef]
  have hqT : q ∈ T := by simp [hTdef]
  have hrT : r ∈ T := by simp [hTdef]
  have hTS' : T ⊆ S' := by
    intro x hx
    simp only [hTdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hTS : T ⊆ S := hTS'.trans hS'
  refine ⟨T, hTS', ?_, ?_⟩
  · rw [hTdef, Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  · -- the point lies in the closure of each of the three (larger) regions
    have hcl : ∀ s : ι, z ∈ frontier (C.VR s S') → z ∈ closure (C.VR s T) := fun s hs =>
      closure_mono (VR_mono hTS') (frontier_subset_closure hs)
    have hclp := hcl p hzp
    have hclq := hcl q hzq
    have hclr := hcl r hzr
    -- and it lies in none of them, since the regions of `T` are pairwise disjoint
    have hnot : ∀ s t : ι, s ∈ T → t ∈ T → s ≠ t → z ∈ closure (C.VR t T) →
        z ∉ C.VR s T := by
      intro s t hsT htT hst hclt hmem
      obtain ⟨y, hy1, hy2⟩ :=
        mem_closure_iff.1 hclt (C.VR s T) (VR_isOpen hTS (hTS hsT)) hmem
      exact (Set.disjoint_left.1 (VR_disjoint hTS hsT htT hst)) hy1 hy2
    have hfront : ∀ s t : ι, s ∈ T → t ∈ T → s ≠ t → z ∈ closure (C.VR s T) →
        z ∈ closure (C.VR t T) → z ∈ frontier (C.VR s T) := by
      intro s t hsT htT hst hcls hclt
      rw [(VR_isOpen hTS (hTS hsT)).frontier_eq]
      exact ⟨hcls, hnot s t hsT htT hst hclt⟩
    exact ⟨p, hpT, q, hqT, r, hrT, hpq, hpr, hqr,
      hfront p q hpT hqT hpq hclp hclq,
      hfront q p hqT hpT (Ne.symm hpq) hclq hclp,
      hfront r p hrT hpT (Ne.symm hpr) hclr hclp⟩

/-- A set with no three pairwise distinct elements is finite of cardinality at most two. -/
theorem finite_and_ncard_le_two {α : Type*} {s : Set α}
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c → False) :
    s.Finite ∧ s.ncard ≤ 2 := by
  classical
  have hfin : s.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := (Set.not_finite.1 hinf).exists_subset_card_eq 3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 htc
    exact h a (hts (by simp)) b (hts (by simp)) c (hts (by simp)) hab hac hbc
  refine ⟨hfin, ?_⟩
  by_contra hgt
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_card_eq (show 3 ≤ s.ncard by omega)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 htc
  exact h a (hts (by simp)) b (hts (by simp)) c (hts (by simp)) hab hac hbc

/-- For a diagram of exactly three sites, a point on the boundaries of three Voronoi regions
lies on the boundary of *every* Voronoi region of the diagram. -/
theorem mem_frontier_VR_of_onBoundaryOfThree {S' : Finset ι} (hcard : S'.card = 3)
    {z : Plane} (hz : C.OnBoundaryOfThree S' z) : ∀ t ∈ S', z ∈ frontier (C.VR t S') := by
  classical
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, hzp, hzq, hzr⟩ := hz
  intro t ht
  have hsub : ({p, q, r} : Finset ι) ⊆ S' := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard3 : ({p, q, r} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  have heq : ({p, q, r} : Finset ι) = S' :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard3])
  rw [← heq] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact hzp
  · exact hzq
  · exact hzr

/-- **Lemma 9** of Klein–Langetepe–Nilforoushan (2009), the case of three sites.

> First, we consider the case where `S = {p₁, p₂, p₃}`.  If one of the three Voronoi regions
> is empty, `V(S)` equals a single bisecting curve, and `B` is empty.  Otherwise, we apply
> the following elegant argument of Thomassen's.  In each Voronoi region `VR(p_j, S)` we
> choose a point denoted by `a_j`.  Now suppose, by way of contradiction, that `B` contains
> three different points, `v₁, v₂, v₃`.  By Lemma 8 and axiom `A₂`, we can find arcs
> `α_{i,j}` connecting `v_i` to `a_j`, such that `α_{i,j} \ {v_i}` is fully contained in
> `VR(p_j, S)`.  We may even assume that for each `j`, the three arcs
> `α_{1,j}, α_{2,j}, α_{3,j}` contained in the region of `p_j` form a plane tree `T_j` rooted
> at `a_j`.  Since the Voronoi regions of `p₁, p₂, p₃` are disjoint, the trees `T₁, T₂, T₃`
> are realizing a plane embedding of the bipartite graph `K₃,₃`, which is impossible.
> Hence, `|B| ⩽ 2` holds.

The proof below follows this argument: Lemma 8 makes each of the three supposed points
accessible from each of the three regions, axiom `A₂` makes the regions path-connected, the
plane trees are provided by `exists_star_of_accessible`, and the contradiction comes from
`noPlaneEmbeddingK33`, the isolated classical fact that `K₃,₃` has no plane embedding. -/
theorem lemma9_three_sites (hadm : C.Admissible) {S' : Finset ι} (hS' : S' ⊆ S)
    (hcard : S'.card = 3) : (C.vertexSet S').Finite ∧ (C.vertexSet S').ncard ≤ 2 := by
  classical
  obtain ⟨p₀, p₁, p₂, h01, h02, h12, hS'eq⟩ := Finset.card_eq_three.1 hcard
  set s : Fin 3 → ι := ![p₀, p₁, p₂] with hsdef
  have hsmem : ∀ j, s j ∈ S' := by
    intro j; fin_cases j <;> simp [hsdef, hS'eq]
  have hsinj : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [h01.symm, h02.symm, h12.symm]
  refine finite_and_ncard_le_two ?_
  intro a ha b hb c hc hab hac hbc
  -- the three supposed Voronoi vertices
  set v : Fin 3 → Plane := ![a, b, c] with hvdef
  have hvmem : ∀ i, v i ∈ C.vertexSet S' := by
    intro i; fin_cases i <;> simpa [hvdef] using ‹_›
  have hvinj : Function.Injective v := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [hab.symm, hac.symm, hbc.symm]
  -- the three Voronoi regions
  set R : Fin 3 → Set Plane := fun j => C.VR (s j) S' with hRdef
  have hRopen : ∀ j, IsOpen (R j) := fun j => VR_isOpen hS' (hS' (hsmem j))
  have hRconn : ∀ j, ∀ x ∈ R j, ∀ y ∈ R j, JoinedIn (R j) x y := fun j =>
    hadm.A2 S' hS' (s j) (hsmem j)
  have hRdisj : ∀ j j', j ≠ j' → Disjoint (R j) (R j') := fun j j' hjj' =>
    VR_disjoint hS' (hsmem j) (hsmem j') fun he => hjj' (hsinj he)
  have hfront : ∀ i j, v i ∈ frontier (R j) := fun i j =>
    mem_frontier_VR_of_onBoundaryOfThree hcard (hvmem i) (s j) (hsmem j)
  have hvnot : ∀ i j, v i ∉ R j := by
    intro i j
    have h := hfront i j
    rw [(hRopen j).frontier_eq] at h
    exact h.2
  -- Lemma 8: each vertex is accessible from each region
  have hacc : ∀ i j, AccessibleFrom (R j) (v i) := fun i j =>
    lemma8 hadm hS' hcard (hsmem j) (hfront i j)
  -- the plane trees of footnote 10
  have hstar : ∀ j, ∃ cj ∈ R j, ∃ β : Fin 3 → (ℝ → Plane),
      (∀ i, IsArc (β i) ∧ β i 0 = v i ∧ β i 1 = cj ∧ β i '' Ioo 0 1 ⊆ R j) ∧
      ∀ i i', i ≠ i' → β i '' Icc 0 1 ∩ β i' '' Icc 0 1 = {cj} := fun j =>
    exists_star_of_accessible (hRopen j) (hRconn j) hvinj (fun i => hvnot i j)
      (fun i => hacc i j)
  choose cc hcc β hβ hβstar using hstar
  -- the nine arcs of the embedding
  have hsubset : ∀ i j, β j i '' Icc 0 1 ⊆ R j ∪ {v i} := by
    intro i j
    rw [image_Icc_eq_union_endpoints]
    rintro x (hx | hx)
    · exact Or.inl ((hβ j i).2.2.2 hx)
    · rcases hx with rfl | rfl
      · exact Or.inr (by rw [(hβ j i).2.1]; rfl)
      · exact Or.inl (by rw [(hβ j i).2.2.1]; exact hcc j)
  have hvmem_arc : ∀ i j, v i ∈ β j i '' Icc 0 1 := by
    intro i j
    exact ⟨0, ⟨le_refl 0, zero_le_one⟩, (hβ j i).2.1⟩
  refine noPlaneEmbeddingK33 v cc (fun i j => β j i) hvinj ?_ (fun i j => (hβ j i).1)
    (fun i j => (hβ j i).2.1) (fun i j => (hβ j i).2.2.1) ?_ ?_ ?_
  · -- the three roots are distinct
    intro j j' hjj'
    by_contra hne
    exact (Set.disjoint_left.1 (hRdisj j j' hne)) (hcc j) (hjj' ▸ hcc j')
  · -- arcs without a common vertex are disjoint
    intro i i' j j' hii' hjj'
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    rcases hsubset i j hx with h | h
    · rcases hsubset i' j' hx' with h' | h'
      · exact (Set.disjoint_left.1 (hRdisj j j' hjj')) h h'
      · exact hvnot i' j (mem_singleton_iff.1 h' ▸ h)
    · rcases hsubset i' j' hx' with h' | h'
      · exact hvnot i j' (mem_singleton_iff.1 h ▸ h')
      · exact hii' (hvinj ((mem_singleton_iff.1 h).symm.trans (mem_singleton_iff.1 h')))
  · -- two arcs at the same `v i` meet exactly in `v i`
    intro i j j' hjj'
    apply Subset.antisymm
    · rintro x ⟨hx, hx'⟩
      rcases hsubset i j hx with h | h
      · rcases hsubset i j' hx' with h' | h'
        · exact absurd ((Set.disjoint_left.1 (hRdisj j j' hjj')) h) (fun hh => hh h')
        · exact absurd (mem_singleton_iff.1 h' ▸ h) (hvnot i j)
      · exact h
    · rintro x hx
      rw [mem_singleton_iff.1 hx]
      exact ⟨hvmem_arc i j, hvmem_arc i j'⟩
  · -- two arcs at the same root meet exactly in the root
    intro i i' j hii'
    exact hβstar j i i' hii'

/-!
## Theorem 10

**Theorem 10** of Klein–Langetepe–Nilforoushan (2009) — the Voronoi diagram is a finite
plane graph — is proved in `AbstractVoronoi.AVD.Edges`, which also contains the sets
`B_{p,q}` used in its proof.
-/

end CurveSystem

end AVD
