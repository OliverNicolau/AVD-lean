import AbstractVoronoi.Paper.Lemma3

/-!
# Lemma 5

**Lemma 5** (the transitivity lemma) of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract
Voronoi diagrams revisited*, Computational Geometry 42 (2009) 885–902.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Lemma 5** (transitivity lemma) of Klein–Langetepe–Nilforoushan (2009).

> Let `p, q, r ∈ S`.  Then `D(p,q) ∩ D(q,r) ⊆ D(p,r)` holds. -/
theorem lemma5 (hadm : C.Admissible) {p q r : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    C.D p q ∩ C.D q r ⊆ C.D p r := by
  have hkey := no_mem_cyclic hadm hp hq hr hpq hqr hpr
  have hkey' : ∀ x ∈ C.D p q ∩ C.D q r, x ∉ C.D r p := by
    intro x hx hx'
    have : x ∈ C.D p q ∩ C.D q r ∩ C.D r p := ⟨hx, hx'⟩
    rw [hkey] at this
    exact this
  intro z hz
  have hznot : z ∉ C.D r p := hkey' z hz
  have hzJ : z ∉ C.J p r := by
    intro hzJ
    -- `z` lies on `J(p,r)`, hence in the closure of `D(r,p)`; but `D(p,q) ∩ D(q,r)` is an
    -- open neighbourhood of `z`, so it would meet `D(r,p)`.
    have hzcl : z ∈ closure (C.D r p) :=
      mem_closure_D_of_mem_J hadm hr hp (Ne.symm hpr)
        (by rw [C.J_symm hr hp (Ne.symm hpr)]; exact hzJ)
    have hopen : IsOpen (C.D p q ∩ C.D q r) :=
      (C.D_isOpen p hp q hq hpq).inter (C.D_isOpen q hq r hr hqr)
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzcl _ hopen hz
    exact hkey' y hy1 hy2
  have : z ∈ (C.J p r)ᶜ := hzJ
  rw [C.compl_J p hp r hr hpr] at this
  rcases this with h | h
  · exact h
  · exact absurd h hznot

end CurveSystem

end AVD
