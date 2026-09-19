import AbstractVoronoi.AVD.Basic

/-!
# Lemma 3

**Lemma 3** of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams
revisited*, Computational Geometry 42 (2009) 885–902: the two alternative descriptions of
the Voronoi diagram `V(S)` of an admissible system of bisecting curves.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Lemma 3** of Klein–Langetepe–Nilforoushan (2009).

> Let `J` be a system of admissible curves for index set `S`.  Then
> `V(S) = ⋃_{p ≠ q ∈ S} closure (VR(p,S)) ∩ J(p,q)`
> `     = ⋃_{p ≠ q ∈ S} closure (VR(p,S)) ∩ closure (VR(q,S))`. -/
theorem lemma3 (hadm : C.Admissible) :
    C.V S = (⋃ p ∈ S, ⋃ q ∈ S.erase p, closure (C.VR p S) ∩ C.J p q) ∧
      C.V S = (⋃ p ∈ S, ⋃ q ∈ S.erase p, closure (C.VR p S) ∩ closure (C.VR q S)) := by
  -- an auxiliary fact used in both inclusions: a point of `V S` lies on the closure of some
  -- region, and on a bisecting curve of that site.
  have key : ∀ z ∈ C.V S, ∃ p ∈ S, ∃ q ∈ S.erase p,
      z ∈ closure (C.VR p S) ∧ z ∈ C.J p q := by
    intro z hz
    have hz' : ∀ p ∈ S, z ∉ C.VR p S := by
      intro p hp hmem
      exact hz (mem_biUnion hp hmem)
    have : z ∈ (⋃ p ∈ S, closure (C.VR p S)) := by rw [hadm.A3 S Subset.rfl]; trivial
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 this
    have hnot : ¬ ∀ q ∈ S.erase p, z ∈ C.D p q := fun h => hz' p hp (mem_VR_iff.2 h)
    push Not at hnot
    obtain ⟨q, hq, hzq⟩ := hnot
    have hqS : q ∈ S := Finset.mem_of_mem_erase hq
    have hpq : p ≠ q := (Finset.ne_of_mem_erase hq).symm
    refine ⟨p, hp, q, hq, hzp, ?_⟩
    refine mem_J_of_notMem hp hqS hpq hzq ?_
    intro hzqp
    -- `D(q,p)` is an open neighbourhood of `z`, hence meets `VR(p,S) ⊆ D(p,q)`
    have hmeet := mem_closure_iff.1 hzp (C.D q p) (C.D_isOpen q hqS p hp (Ne.symm hpq)) hzqp
    obtain ⟨y, hy1, hy2⟩ := hmeet
    have : y ∈ C.D p q := VR_subset_D hq hy2
    exact (Set.disjoint_left.1 (C.D_disjoint p hp q hqS hpq)) this hy1
  constructor
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨p, hp, q, hq, h1, h2⟩ := key z hz
      exact mem_biUnion hp (mem_biUnion hq ⟨h1, h2⟩)
    · intro z hz
      obtain ⟨p, hp, hz⟩ := mem_iUnion₂.1 hz
      obtain ⟨q, hq, hz1, hz2⟩ := mem_iUnion₂.1 hz
      have hqS : q ∈ S := Finset.mem_of_mem_erase hq
      have hpq : p ≠ q := (Finset.ne_of_mem_erase hq).symm
      intro hmem
      obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hmem
      rcases eq_or_ne s p with rfl | hsp
      · exact (notMem_D_of_mem_J hp hqS hpq hz2).1 (VR_subset_D hq hzs)
      · obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hz1 (C.VR s S) (VR_isOpen Subset.rfl hs) hzs
        exact (Set.disjoint_left.1 (VR_disjoint Subset.rfl hp hs (Ne.symm hsp))) hy2 hy1
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨p, hp, q, hq, h1, h2⟩ := key z hz
      have hqS : q ∈ S := Finset.mem_of_mem_erase hq
      have hpq : p ≠ q := (Finset.ne_of_mem_erase hq).symm
      -- the set of points lying in the closure of a region other than that of `p`
      set T : Set Plane := ⋃ s ∈ S.erase p, closure (C.VR s S) with hT
      have hTclosed : IsClosed T := by
        refine Set.Finite.isClosed_biUnion (S.erase p).finite_toSet ?_
        intro s _
        exact isClosed_closure
      have hsub : C.D q p ⊆ T := by
        intro x hx
        have : x ∈ (⋃ s ∈ S, closure (C.VR s S)) := by rw [hadm.A3 S Subset.rfl]; trivial
        obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 this
        rcases eq_or_ne s p with rfl | hsp
        · exfalso
          have hxcl : x ∈ closure (C.D s q) :=
            closure_mono (fun y hy => VR_subset_D hq hy) hxs
          rw [closure_D_eq hadm hp hqS hpq] at hxcl
          rcases hxcl with h | h
          · exact (Set.disjoint_left.1 (C.D_disjoint s hp q hqS hpq)) h hx
          · exact (notMem_D_of_mem_J hp hqS hpq h).2 hx
        · exact mem_biUnion (Finset.mem_erase.2 ⟨hsp, hs⟩) hxs
      have hzT : z ∈ T := by
        have hzcl : z ∈ closure (C.D q p) :=
          mem_closure_D_of_mem_J hadm hqS hp (Ne.symm hpq)
            (by rw [C.J_symm hqS hp (Ne.symm hpq)]; exact h2)
        have := closure_mono hsub hzcl
        rwa [hTclosed.closure_eq] at this
      obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hzT
      exact mem_biUnion hp (mem_biUnion hs ⟨h1, hzs⟩)
    · intro z hz
      obtain ⟨p, hp, hz⟩ := mem_iUnion₂.1 hz
      obtain ⟨q, hq, hz1, hz2⟩ := mem_iUnion₂.1 hz
      exact mem_V_of_two_closures hp (Finset.mem_of_mem_erase hq)
        ((Finset.ne_of_mem_erase hq).symm) hz1 hz2

end CurveSystem

end AVD
