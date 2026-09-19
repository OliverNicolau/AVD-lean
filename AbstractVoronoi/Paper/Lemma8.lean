import AbstractVoronoi.AVD.AAConfiguration

/-!
# Lemma 8

**Lemma 8** of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams
revisited*, Computational Geometry 42 (2009) 885–902: in the Voronoi diagram of three
sites, every point on the boundary of a Voronoi region is accessible from that region.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Lemma 8** of Klein–Langetepe–Nilforoushan (2009).

> Let `w` be a point on the boundary of `VR(p, S)`, where `|S| = 3`.  Then there exists an
> arc `α` with endpoint `w` such that `α \ {w} ⊆ VR(p, S)` holds.

The three sites form a subset `S' ⊆ S` of size three, and the Voronoi regions are taken
with respect to `S'`.  The case in which `w` lies on both bisecting curves through `p` is
`lemma8_common_point`; the two cases in which `w` lies on only one of them are settled here
directly from Theorem 4. -/
theorem lemma8 (hadm : C.Admissible) {S' : Finset ι} (hS' : S' ⊆ S) (hcard : S'.card = 3)
    {p : ι} (hp : p ∈ S') {w : Plane} (hw : w ∈ frontier (C.VR p S')) :
    AccessibleFrom (C.VR p S') w := by
  -- name the two other sites
  have hcard2 : (S'.erase p).card = 2 := by
    rw [Finset.card_erase_of_mem hp, hcard]
  obtain ⟨q, r, hqr, hqr'⟩ := Finset.card_eq_two.1 hcard2
  have hqS' : q ∈ S' := Finset.mem_of_mem_erase (by rw [hqr']; simp)
  have hrS' : r ∈ S' := Finset.mem_of_mem_erase (by rw [hqr']; simp)
  have hpq : p ≠ q := (Finset.ne_of_mem_erase (by rw [hqr']; simp)).symm
  have hpr : p ≠ r := (Finset.ne_of_mem_erase (by rw [hqr']; simp)).symm
  have hS'eq : S' = {p, q, r} := by
    rw [← Finset.insert_erase hp, hqr']
  have hpS : p ∈ S := hS' hp
  have hqS : q ∈ S := hS' hqS'
  have hrS : r ∈ S := hS' hrS'
  subst hS'eq
  have hVR : C.VR p {p, q, r} = C.D p q ∩ C.D p r := VR_triple rfl hpq hpr
  rw [(VR_isOpen hS' hpS).frontier_eq] at hw
  obtain ⟨hwcl, hwnot⟩ := hw
  -- `w` is in the closure of both half-planes of `p`
  have hclosure : ∀ X : ι, X ∈ S → p ≠ X → (∀ y ∈ C.VR p {p, q, r}, y ∈ C.D p X) →
      w ∉ C.D X p := by
    intro X hX hpX hsub hwX
    obtain ⟨y, hy1, hy2⟩ :=
      mem_closure_iff.1 hwcl (C.D X p) (C.D_isOpen X hX p hpS (Ne.symm hpX)) hwX
    exact (Set.disjoint_left.1 (C.D_disjoint p hpS X hX hpX)) (hsub y hy2) hy1
  have hwq : w ∉ C.D q p := hclosure q hqS hpq (fun y hy => by rw [hVR] at hy; exact hy.1)
  have hwr : w ∉ C.D r p := hclosure r hrS hpr (fun y hy => by rw [hVR] at hy; exact hy.2)
  -- and it is not in their intersection
  have hwnot' : w ∉ C.D p q ∨ w ∉ C.D p r := by
    by_contra hcon
    push Not at hcon
    exact hwnot (hVR ▸ ⟨hcon.1, hcon.2⟩)
  rcases hwnot' with h | h
  · -- `w` lies on `J(p,q)`
    have hwJq : w ∈ C.J p q := mem_J_of_notMem hpS hqS hpq h hwq
    by_cases hwDr : w ∈ C.D p r
    · -- and inside the other half-plane: accessibility from `D(p,r) ∩ D(p,q)`
      refine AccessibleFrom.mono ?_
        (accessibleFrom_of_mem_J hadm hpS hqS hpq hwJq
          ((C.D_isOpen p hpS r hrS hpr).mem_nhds hwDr))
      rw [hVR]
      exact fun y hy => ⟨hy.2, hy.1⟩
    · exact lemma8_common_point hadm hpS hqS hrS hpq hqr hpr hwJq
        (mem_J_of_notMem hpS hrS hpr hwDr hwr)
        (by rw [(VR_isOpen hS' hpS).frontier_eq]; exact ⟨hwcl, hwnot⟩)
  · -- `w` lies on `J(p,r)`
    have hwJr : w ∈ C.J p r := mem_J_of_notMem hpS hrS hpr h hwr
    by_cases hwDq : w ∈ C.D p q
    · refine AccessibleFrom.mono ?_
        (accessibleFrom_of_mem_J hadm hpS hrS hpr hwJr
          ((C.D_isOpen p hpS q hqS hpq).mem_nhds hwDq))
      rw [hVR]
    · exact lemma8_common_point hadm hpS hqS hrS hpq hqr hpr
        (mem_J_of_notMem hpS hqS hpq hwDq hwq) hwJr
        (by rw [(VR_isOpen hS' hpS).frontier_eq]; exact ⟨hwcl, hwnot⟩)

end CurveSystem

end AVD
