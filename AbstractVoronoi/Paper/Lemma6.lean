import AbstractVoronoi.AVD.ThreeSites

/-!
# Lemma 6

**Lemma 6** of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams
revisited*, Computational Geometry 42 (2009) 885–902: for three sites, a point of
`J(p,q)` that is accessible from the Voronoi regions of `p` and of `r` lies on `J(p,r)`.
The construction behind it is the auxiliary `AVD.CurveSystem.lemma6_core` of
`AbstractVoronoi.AVD.ThreeSites`.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **Lemma 6** of Klein–Langetepe–Nilforoushan (2009).

> There cannot be four points consecutively visited by `J(p,r)` that belong alternately to
> `D(p,q)` and `D(q,p)`.

Here "consecutively visited" is expressed through a parametrization `g` of the curve
`J(p,r)`: the four points are `g t₁, g t₂, g t₃, g t₄` with `t₁ < t₂ < t₃ < t₄`, and
"alternately" allows both patterns.  As in Subsection 3.1 of the paper, three sites
`p, q, r ∈ S` are involved. -/
theorem lemma6 (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p r))
    {t₁ t₂ t₃ t₄ : ℝ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h34 : t₃ < t₄) :
    ¬ ((g t₁ ∈ C.D q p ∧ g t₂ ∈ C.D p q ∧ g t₃ ∈ C.D q p ∧ g t₄ ∈ C.D p q) ∨
       (g t₁ ∈ C.D p q ∧ g t₂ ∈ C.D q p ∧ g t₃ ∈ C.D p q ∧ g t₄ ∈ C.D q p)) := by
  rintro (⟨ha1, ha2, ha3, ha4⟩ | ⟨ha1, ha2, ha3, ha4⟩)
  · exact lemma6_core hadm hp hq hr hpq hqr hpr hg (h23.trans h34) h23 h34
      (Or.inl h12) ha2 ha4 ha3 ha1
  · exact lemma6_core hadm hp hq hr hpq hqr hpr hg (h12.trans h23) h12 h23
      (Or.inr h34) ha1 ha3 ha2 ha4

end CurveSystem

end AVD
