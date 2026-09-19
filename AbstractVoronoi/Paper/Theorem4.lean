import AbstractVoronoi.Jordan.UnboundedLocal

/-!
# Theorem 4

This file states and proves **Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

from the sole topological assumption of the development,
`AVD.jordanCurveLocalConnectedness`: the complementary domains of a Jordan curve are locally
connected at each point of the curve.

Its *global* part is proved with no assumption at all
(`AVD.IsClosedJordanCurve.exists_separation_frontier_eq` and
`AVD.IsUnboundedJordanCurve.exists_separation_frontier_eq`), and its *local* part is
`AVD.IsClosedJordanCurve.exists_local_nbhd` for closed Jordan curves and
`AVD.IsUnboundedJordanCurve.exists_local_nbhd` for the unbounded curves of axiom `A₁`.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- **Theorem 4** of Klein–Langetepe–Nilforoushan (2009), stated as a proposition.

> Let `C` be a plane curve, homeomorphic to a circle.  Then `ℝ² \ C` consists of two domains
> `D₁, D₂` with common boundary `C`.  For each point `z ∈ C` there exists a neighbourhood `U`
> whose boundary is homeomorphic to a circle, such that `U \ C` consists of exactly two
> connected components.  Point `z` is accessible from each domain `U ∩ Dᵢ`, that is, for each
> `p ∈ U ∩ Dᵢ` there exists an arc `α` from `p` to `z` such that `α` minus its endpoint `z`
> belongs to `U ∩ Dᵢ`.

Three remarks on the formalisation.

* As the paper does (see the discussion following Theorem 4), the statement is used for
  closed Jordan curves *and* for their unbounded analogues, i.e. for `IsJordanCurve`; for a
  closed curve, one of the two domains (the *interior domain*) is bounded and the other one
  is not.
* "there exists a neighbourhood `U`" is strengthened to "arbitrarily small neighbourhoods
  `U` exist", which is how the paper uses the theorem ("we can make `U` small enough").
* Theorem 4 is a consequence of the Jordan–Schönflies theorem, which is not part of
  `Mathlib`.  Its global part — the separation of the plane into two domains with common
  boundary `C` — is *proved* here, in `AbstractVoronoi.Jordan.Schoenflies` for closed Jordan
  curves and in `AbstractVoronoi.Jordan.SphereTransfer` for the unbounded curves of axiom
  `A₁`; its local part is isolated as `AVD.JordanCurveLocalAccessibility` and is *proved*
  below from the local connectedness of the two complementary domains at the points of the
  curve (`AVD.jordanCurveLocalConnectedness`), itself proved from the Jordan–Schönflies
  theorem of the dependency.  Theorem 4 therefore carries no unproved hypothesis. -/
def JordanCurveAccessibility : Prop :=
  ∀ C : Set Plane, IsJordanCurve C →
    ∃ D₁ D₂ : Set Plane,
      IsOpen D₁ ∧ IsOpen D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧ Disjoint D₁ D₂ ∧
      D₁ ∪ D₂ = Cᶜ ∧ frontier D₁ = C ∧ frontier D₂ = C ∧
      (IsClosedJordanCurve C →
        (Bornology.IsBounded D₁ ∧ ¬ Bornology.IsBounded D₂) ∨
        (Bornology.IsBounded D₂ ∧ ¬ Bornology.IsBounded D₁)) ∧
      ∀ z ∈ C, ∀ V ∈ 𝓝 z, ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧
        IsClosedJordanCurve (frontier U) ∧
        IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
        (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
        (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z)

/-- The **local** part of Theorem 4 of Klein–Langetepe–Nilforoushan (2009); see
`AVD.JordanCurveLocalAccessibility` for the statement.

This is the Jordan–Schönflies content of Theorem 4, which the paper quotes from Rinow's
book.  It is *proved* here from the local connectedness of the two complementary domains at
the points of the curve (`AVD.jordanCurveLocalConnectedness`), by the construction of
`AbstractVoronoi.Jordan.LocalAccessibility` for a closed Jordan curve and by that of
`AbstractVoronoi.Jordan.UnboundedLocal` for the unbounded curves of axiom `A₁`. -/
theorem jordanCurveLocalAccessibility : JordanCurveLocalAccessibility := by
  intro C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 z hz V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  have hlc1 : ∀ y ∈ C, LocallyConnectedAt D₁ y := fun y hy =>
    jordanCurveLocalConnectedness C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 y hy
  have hlc2 : ∀ y ∈ C, LocallyConnectedAt D₂ y := fun y hy =>
    jordanCurveLocalConnectedness C hC D₂ D₁ h2o h1o h2c h1c hdisj.symm
      (by rw [union_comm]; exact hunion) hf2 hf1 y hy
  have key : ∃ U : Set Plane, IsOpen U ∧ z ∈ U ∧ U ⊆ ball z ε ∧
      IsClosedJordanCurve (frontier U) ∧
      IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
      (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
      (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z) := by
    rcases hC with hcl | hub
    · exact hcl.exists_local_nbhd h1o h2o hdisj hunion hf1 hf2 hlc1 hlc2 hz hε
    · exact hub.exists_local_nbhd h1o h2o hdisj hunion hf1 hf2 hlc1 hlc2 hz hε
  obtain ⟨U, hUopen, hzU, hUball, hJ, hc1, hc2, hacc1, hacc2⟩ := key
  exact ⟨U, hUopen.mem_nhds hzU, fun w hw => hεV (hUball hw), hUopen, hJ, hc1, hc2,
    hacc1, hacc2⟩

/-- **Theorem 4** of Klein–Langetepe–Nilforoushan (2009).

> Let `C` be a plane curve, homeomorphic to a circle.  Then `ℝ² \ C` consists of two domains
> `D₁, D₂` with common boundary `C`.  For each point `z ∈ C` there exists a neighbourhood `U`
> whose boundary is homeomorphic to a circle, such that `U \ C` consists of exactly two
> connected components.  Point `z` is accessible from each domain `U ∩ Dᵢ`, that is, for each
> `p ∈ U ∩ Dᵢ` there exists an arc `α` from `p` to `z` such that `α` minus its endpoint `z`
> belongs to `U ∩ Dᵢ`.

This is the classical Jordan curve theorem in its accessibility form, quoted in the paper
from Rinow's book as a consequence of the Jordan–Schönflies theorem.  As the paper does, the
statement is used both for closed Jordan curves and for the unbounded curves of axiom `A₁`.

Its **global** part is proved in this development, with no assumption: for a closed Jordan
curve it is `AVD.IsClosedJordanCurve.exists_separation_frontier_eq` (the Jordan curve
theorem of the Lean 4 Jordan–Schönflies development this project depends on, together with
the non-separation theorem for arcs, which gives that the boundary of each domain is *all*
of `C`), and for a curve satisfying axiom `A₁` it is
`AVD.IsUnboundedJordanCurve.exists_separation_frontier_eq`, obtained from the former by the
transfer through the sphere that the paper performs.

Its **local** part is `AVD.jordanCurveLocalAccessibility`, proved from the local
connectedness of the two complementary domains at the points of the curve
(`AVD.jordanCurveLocalConnectedness`), which is in turn proved from the Jordan–Schönflies
theorem of the dependency.  The whole of Theorem 4 is therefore proved here, with no
assumption. -/
theorem theorem4 : JordanCurveAccessibility := by
  intro C hC
  by_cases hcl : IsClosedJordanCurve C
  · obtain ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, hf1, hf2, hbdd⟩ :=
      hcl.exists_separation_frontier_eq
    exact ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, hf1, hf2, fun _ => hbdd,
      jordanCurveLocalAccessibility C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2⟩
  · have hub : IsUnboundedJordanCurve C := hC.resolve_left hcl
    obtain ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, hf1, hf2⟩ :=
      hub.exists_separation_frontier_eq
    exact ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj, hunion, hf1, hf2, fun h => absurd h hcl,
      jordanCurveLocalAccessibility C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2⟩

end AVD
