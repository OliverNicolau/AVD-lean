import AbstractVoronoi.Jordan.SupNorm
import Schoenflies

/-!
# The planar-topology backend

This file is the **only** place where the development uses an external formalization of
planar topology.  It states, for the plane `EuclideanSpace ℝ (Fin 2)`, the results that the
rest of the project takes from outside, and proves them from

* Á. Begué, *The Jordan–Schönflies theorem in Lean*,
  <https://github.com/alonamaloh/schoenflies-lean> (Apache License 2.0).

Every other file reaches that development only through the declarations below, so this
file is the trust boundary of the project, and replacing the backend means re-proving
exactly these statements.

## Statements

* `Backend.IsArc`, `Backend.IsArcBetween`, `Backend.IsJordanCurve`: set-level simple arcs
  and Jordan curves (images of `[0,1]`).
* `Backend.jordan_curve_theorem`: a Jordan curve splits the plane into two disjoint
  connected open domains.
* `Backend.exists_arcBetween_of_isPreconnected`: two distinct points of a connected open set
  are joined by a simple arc inside it.
* `Backend.exists_arcBetween_compl_arc`: two distinct points off a simple arc are joined by a
  simple arc off it.
* `Backend.jordan_schoenflies_of_homeomorph`: a homeomorphism between two Jordan curves
  extends to a homeomorphism of the plane.
* `Backend.isJordanCurve_modelCurve`, `Backend.IsJordanCurve.nonempty_homeomorph_modelCurve`:
  the boundary of the square `[-1,1]²` is a Jordan curve, homeomorphic to every Jordan curve.
-/

noncomputable section

open Set

namespace AVD

namespace Backend

/-- The plane, written out (this file sits below `AbstractVoronoi/Jordan/Sphere.lean`, where
the abbreviation `AVD.Plane` is introduced; the two are the same type). -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## Definitions -/

/-- A simple arc: the image of `[0,1]` under a map continuous and injective there. -/
def IsArc (A : Set ℝ²) : Prop :=
  ∃ f : ℝ → ℝ², ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f '' Icc 0 1 = A

/-- A simple arc from `p` to `q`. -/
def IsArcBetween (A : Set ℝ²) (p q : ℝ²) : Prop :=
  ∃ f : ℝ → ℝ², ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f '' Icc 0 1 = A ∧
    f 0 = p ∧ f 1 = q

/-- A Jordan curve: the image of `[0,1]` under a map continuous there, injective on `[0,1)`,
taking the same value at `0` and `1`. -/
def IsJordanCurve (C : Set ℝ²) : Prop :=
  ∃ f : ℝ → ℝ², ContinuousOn f (Icc 0 1) ∧ f 0 = f 1 ∧ InjOn f (Ico 0 1) ∧
    f '' Icc 0 1 = C

/-! ## Translation to the notions of the dependency -/

theorem isArc_iff {A : Set ℝ²} : IsArc A ↔ Schoenflies.IsArc A := Iff.rfl

theorem isArcBetween_iff {A : Set ℝ²} {p q : ℝ²} :
    IsArcBetween A p q ↔ Schoenflies.IsArcBetween A p q := Iff.rfl

theorem isJordanCurve_iff {C : Set ℝ²} : IsJordanCurve C ↔ Schoenflies.IsJordanCurve C := by
  constructor
  · rintro ⟨f, hcont, hcl, hinj, himg⟩
    exact ⟨f, ⟨hcont, hcl, hinj⟩, himg⟩
  · rintro ⟨f, ⟨hcont, hcl, hinj⟩, himg⟩
    exact ⟨f, hcont, hcl, hinj, himg⟩

/-! ## The statements -/

/-- **The Jordan curve theorem.**  The complement of a Jordan curve is the union of two
disjoint connected open sets. -/
theorem jordan_curve_theorem {C : Set ℝ²} (hC : IsJordanCurve C) :
    ∃ A B : Set ℝ², IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = univ := by
  have hsep := Schoenflies.jordan_curve_theorem (isJordanCurve_iff.1 hC)
  refine ⟨Schoenflies.inside C, Schoenflies.outside C, hsep.isOpen_inside, hsep.isOpen_outside,
    hsep.isConnected_inside, hsep.isConnected_outside, Schoenflies.disjoint_inside_outside,
    ?_, ?_, ?_⟩
  · exact Set.disjoint_left.2 fun x hx => Schoenflies.inside_subset_compl hx
  · exact Set.disjoint_left.2 fun x hx => Schoenflies.outside_subset_compl hx
  · rw [Schoenflies.inside_union_outside]
    exact compl_union_self C

/-- Two distinct points of a connected open subset of the plane are joined by a simple arc
inside it. -/
theorem exists_arcBetween_of_isPreconnected {Ω : Set ℝ²} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {x y : ℝ²} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ A ⊆ Ω, IsArcBetween A x y := by
  obtain ⟨A, hAΩ, -, harc⟩ := Schoenflies.exists_simple_arc_of_isPreconnected hΩ hconn hx hy hxy
  exact ⟨A, hAΩ, harc⟩

/-- Two distinct points off a simple arc are joined by a simple arc that avoids it. -/
theorem exists_arcBetween_compl_arc {A : Set ℝ²} (hA : IsArc A) {u w : ℝ²} (huw : u ≠ w)
    (hu : u ∉ A) (hw : w ∉ A) : ∃ P : Set ℝ², IsArcBetween P u w ∧ P ⊆ Aᶜ := by
  obtain ⟨P, -, hP, hPA⟩ := Schoenflies.arc_complement_poly hA huw hu hw
  exact ⟨P, hP, hPA⟩

/-- **The Jordan–Schönflies theorem.**  Every homeomorphism between two Jordan curves extends
to a homeomorphism of the plane. -/
theorem jordan_schoenflies_of_homeomorph {C C' : Set ℝ²} (hC : IsJordanCurve C)
    (hC' : IsJordanCurve C') (e : C ≃ₜ C') : ∃ F : ℝ² ≃ₜ ℝ², ∀ z : C, F z = e z :=
  Schoenflies.jordan_schoenflies_of_homeomorph (isJordanCurve_iff.1 hC)
    (isJordanCurve_iff.1 hC') e

/-- The model curve, the boundary of the square `[-1,1]²`, is a Jordan curve. -/
theorem isJordanCurve_modelCurve : IsJordanCurve Square.modelCurve :=
  isJordanCurve_iff.2 Schoenflies.isJordanCurve_modelCurve

/-- Every Jordan curve is homeomorphic to the model curve. -/
theorem IsJordanCurve.nonempty_homeomorph_modelCurve {C : Set ℝ²} (hC : IsJordanCurve C) :
    Nonempty (C ≃ₜ Square.modelCurve) :=
  Schoenflies.IsJordanCurve.homeomorph_modelCurve (isJordanCurve_iff.1 hC)

end Backend

end AVD
