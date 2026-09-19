import AbstractVoronoi.AVD.Graph

/-!
# Lemma 9

**Lemma 9** of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams
revisited*, Computational Geometry 42 (2009) 885–902: the points lying on the boundaries of
at least three Voronoi regions of some subdiagram of an admissible system are finitely many,
at most `2 * C(n,3)`.  The three-site case is the auxiliary
`AVD.CurveSystem.lemma9_three_sites` of `AbstractVoronoi.AVD.Graph`, which follows
Thomassen's argument through the non-planarity of `K(3,3)`.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Lemma 9** of Klein–Langetepe–Nilforoushan (2009).

> Let `B` be the set of all points on the boundaries of at least three Voronoi regions in
> some Voronoi diagram `V(S')`, where `S' ⊆ S`.  If `|S| = n ⩾ 3` then `B` is of size at most
> `2·C(n,3)`.

The paper states the bound under the hypothesis `n ⩾ 3`; that hypothesis turns out not to be
needed, since for `|S| < 3` both sides of the inequality are `0`, so it is omitted here. -/
theorem lemma9 (hadm : C.Admissible) :
    C.BSet.Finite ∧ C.BSet.ncard ≤ 2 * (S.card.choose 3) := by
  have hsub : C.BSet ⊆ ⋃ T ∈ S.powersetCard 3, C.vertexSet T := by
    rintro z ⟨S', hS', hz⟩
    obtain ⟨T, hTS', hTcard, hzT⟩ := exists_triple_of_onBoundaryOfThree hS' hz
    exact mem_biUnion (Finset.mem_powersetCard.2 ⟨hTS'.trans hS', hTcard⟩) hzT
  have hfin : ∀ T ∈ S.powersetCard 3, (C.vertexSet T).Finite := by
    intro T hT
    obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.1 hT
    exact (lemma9_three_sites hadm hTS hTcard).1
  have hbig : (⋃ T ∈ S.powersetCard 3, C.vertexSet T).Finite :=
    Set.Finite.biUnion (S.powersetCard 3).finite_toSet hfin
  refine ⟨hbig.subset hsub, ?_⟩
  calc C.BSet.ncard ≤ (⋃ T ∈ S.powersetCard 3, C.vertexSet T).ncard :=
        Set.ncard_le_ncard hsub hbig
    _ ≤ ∑ T ∈ S.powersetCard 3, (C.vertexSet T).ncard :=
        Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _T ∈ S.powersetCard 3, 2 := by
        refine Finset.sum_le_sum fun T hT => ?_
        obtain ⟨hTS, hTcard⟩ := Finset.mem_powersetCard.1 hT
        exact (lemma9_three_sites hadm hTS hTcard).2
    _ = 2 * (S.card.choose 3) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, Nat.mul_comm]

end CurveSystem

end AVD
