import AbstractVoronoi.Jordan.ArcFacts

/-!
# Definition 1 and Definition 2 of the paper

This file contains the formal counterparts of the **definitions** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

and nothing else; the auxiliary API about them lives in `AbstractVoronoi.AVD.Basic`.

* the data of a system of bisecting curves (beginning of Section 2): `AVD.CurveSystem`;
* the Voronoi region `VR(p, S')` of equation (1) and the Voronoi diagram `V(S')` of
  equation (2): `AVD.CurveSystem.VR` and `AVD.CurveSystem.V`;
* **Definition 1**, the three axioms `A₁`, `A₂`, `A₃` of an admissible system of bisecting
  curves: `AVD.CurveSystem.Admissible`;
* **Definition 2**, the Voronoi region and the Voronoi diagram of an admissible system:
  `AVD.CurveSystem.voronoiRegion` and `AVD.CurveSystem.voronoiDiagram`.
-/

noncomputable section

open Set Topology

namespace AVD

variable {ι : Type*} [DecidableEq ι]

/-- The data of a system of bisecting curves, as described at the beginning of Section 2 of
Klein–Langetepe–Nilforoushan (2009):

> We are given a finite set `S` of indices (representing sites), and, for any two indices
> `p ≠ q` of `S`, a curve `J(p,q) = J(q,p)` that splits the plane into two unbounded domains,
> labeled `D(p,q)` and `D(q,p)`.

The labelling is part of the data.  (For pairs of indices outside `S`, or for `p = q`, the
values of `J` and `D` are unconstrained and irrelevant.)

The formal definition is deliberately *slightly more general* than the printed one: the
paper requires each `J(p,q)` to split the plane into two **unbounded domains**, whereas the
structure below only asks that the two labelled pieces `D(p,q)`, `D(q,p)` be open, disjoint,
preconnected, and complementary to `J(p,q)`.  Nothing is lost, because for an *admissible*
system (Definition 1) the missing properties are theorems rather than hypotheses: axiom
`A₁` forces both pieces to be non-empty (`AVD.CurveSystem.D_nonempty`), hence connected
(`AVD.CurveSystem.D_isConnected`), and unbounded
(`AVD.CurveSystem.D_not_isBounded`). -/
structure CurveSystem (S : Finset ι) where
  /-- The bisecting curve of `p` and `q`. -/
  J : ι → ι → Set Plane
  /-- The open domain ("half-plane") of `J p q` labelled by `p`. -/
  D : ι → ι → Set Plane
  /-- The two domains of a bisecting curve are open. -/
  D_isOpen : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsOpen (D p q)
  /-- The two domains of a bisecting curve are preconnected.  (For an admissible system they
  are non-empty, hence domains in the sense of the paper; see
  `AVD.CurveSystem.D_isConnected`.) -/
  D_isPreconnected : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsPreconnected (D p q)
  /-- The two domains of a bisecting curve are disjoint. -/
  D_disjoint : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (D p q) (D q p)
  /-- The curve `J(p,q)` splits the plane into the two domains `D(p,q)` and `D(q,p)`. -/
  compl_J : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → (J p q)ᶜ = D p q ∪ D q p

namespace CurveSystem

variable {S : Finset ι} (C : CurveSystem S)

/-- Equation (1) of Klein–Langetepe–Nilforoushan (2009):
`VR(p, S') := ⋂_{q ∈ S' \ {p}} D(p,q)`. -/
def VR (p : ι) (S' : Finset ι) : Set Plane := ⋂ q ∈ S'.erase p, C.D p q

/-- Equation (2) of Klein–Langetepe–Nilforoushan (2009):
`V(S') := ℝ² \ ⋃_{p ∈ S'} VR(p, S')`. -/
def V (S' : Finset ι) : Set Plane := (⋃ p ∈ S', C.VR p S')ᶜ

/-- **Definition 1** of Klein–Langetepe–Nilforoushan (2009).

> The curve system `J := {J(p,q); p ≠ q ∈ S}` is called *admissible* if the following axioms
> are fulfilled.
> * `A₁`) Each curve `J(p,q)`, where `p, q ∈ S`, is mapped to a closed Jordan curve through
>   the north pole by stereographic projection to the sphere.
> * `A₂`) For each subset `S' ⊆ S` and for each `p' ∈ S'`, the set `VR(p', S')` is
>   path-connected.
> * `A₃`) For each subset `S' ⊆ S`, we have `ℝ² = ⋃_{p' ∈ S'} closure (VR(p', S'))`.

Axiom `A₁` is rendered by `IsUnboundedJordanCurve`, which is stated exactly as in the paper:
the inverse stereographic image of the curve on the sphere `S²`, completed by the north
pole, is a closed Jordan curve (cf. footnote 4 of the paper).  Such a curve is a properly
embedded line of the plane; this is the content of
`IsUnboundedJordanCurve.exists_properParam`, which produces the parametrizations `ℝ → ℝ²`
used in Lemmas 6 to 8.  Axiom `A₂` is stated in the form "any two points of
`VR(p', S')` can be joined by a path inside it", so that empty regions are allowed, as they
must be (see the proof of Lemma 9 in the paper). -/
structure Admissible : Prop where
  /-- Axiom `A₁`. -/
  A1 : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsUnboundedJordanCurve (C.J p q)
  /-- Axiom `A₂`. -/
  A2 : ∀ S' ⊆ S, ∀ p ∈ S', ∀ x ∈ C.VR p S', ∀ y ∈ C.VR p S', JoinedIn (C.VR p S') x y
  /-- Axiom `A₃`. -/
  A3 : ∀ S' ⊆ S, (⋃ p ∈ S', closure (C.VR p S')) = univ

/-- **Definition 2** of Klein–Langetepe–Nilforoushan (2009): for an admissible curve system
`J`, the set `VR(p, S)` is called the *Voronoi region* of `p` with respect to `S`. -/
def voronoiRegion (p : ι) (S' : Finset ι) : Set Plane := C.VR p S'

/-- **Definition 2** of Klein–Langetepe–Nilforoushan (2009): for an admissible curve system
`J`, the set `V(S)` is called the *Voronoi diagram* of `S`. -/
def voronoiDiagram (S' : Finset ι) : Set Plane := C.V S'

@[simp] theorem voronoiRegion_eq (p : ι) (S' : Finset ι) :
    C.voronoiRegion p S' = C.VR p S' := rfl

@[simp] theorem voronoiDiagram_eq (S' : Finset ι) : C.voronoiDiagram S' = C.V S' := rfl

end CurveSystem

end AVD
