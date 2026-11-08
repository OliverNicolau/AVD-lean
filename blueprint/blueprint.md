# Abstract Voronoi diagrams revisited — blueprint of the Lean 4 formalization

Generated from the Lean sources in `AbstractVoronoi/Paper/` by `blueprint/generate.py`.  For each numbered statement of Klein, Langetepe and Nilforoushan (2009) it shows the statement of the paper, the remarks on the formalization, and the Lean statement.

## Bisecting curve systems

*Source: `AbstractVoronoi/Paper/Definitions.lean`*

 The data of a system of bisecting curves, as described at the beginning of Section 2 of
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
(`AVD.CurveSystem.D_not_isBounded`). 

```lean
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
```

## The Voronoi region (1) and the Voronoi diagram (2)

*Source: `AbstractVoronoi/Paper/Definitions.lean`*

 Equation (1) of Klein–Langetepe–Nilforoushan (2009):
`VR(p, S') := ⋂_{q ∈ S' \ {p}} D(p,q)`. 

```lean
def VR (p : ι) (S' : Finset ι) : Set Plane := ⋂ q ∈ S'.erase p, C.D p q
```

 Equation (2) of Klein–Langetepe–Nilforoushan (2009):
`V(S') := ℝ² \ ⋃_{p ∈ S'} VR(p, S')`. 

```lean
def V (S' : Finset ι) : Set Plane := (⋃ p ∈ S', C.VR p S')ᶜ
```

## Definition 1

*Source: `AbstractVoronoi/Paper/Definitions.lean`*

 **Definition 1** of Klein–Langetepe–Nilforoushan (2009).

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
must be (see the proof of Lemma 9 in the paper). 

```lean
structure Admissible : Prop where
  /-- Axiom `A₁`. -/
  A1 : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsUnboundedJordanCurve (C.J p q)
  /-- Axiom `A₂`. -/
  A2 : ∀ S' ⊆ S, ∀ p ∈ S', ∀ x ∈ C.VR p S', ∀ y ∈ C.VR p S', JoinedIn (C.VR p S') x y
  /-- Axiom `A₃`. -/
  A3 : ∀ S' ⊆ S, (⋃ p ∈ S', closure (C.VR p S')) = univ
```

## Definition 2

*Source: `AbstractVoronoi/Paper/Definitions.lean`*

 **Definition 2** of Klein–Langetepe–Nilforoushan (2009): for an admissible curve system
`J`, the set `VR(p, S)` is called the *Voronoi region* of `p` with respect to `S`. 

```lean
def voronoiRegion (p : ι) (S' : Finset ι) : Set Plane := C.VR p S'
```

 **Definition 2** of Klein–Langetepe–Nilforoushan (2009): for an admissible curve system
`J`, the set `V(S)` is called the *Voronoi diagram* of `S`. 

```lean
def voronoiDiagram (S' : Finset ι) : Set Plane := C.V S'
```

## Lemma 3

*Source: `AbstractVoronoi/Paper/Lemma3.lean`*

 **Lemma 3** of Klein–Langetepe–Nilforoushan (2009).

> Let `J` be a system of admissible curves for index set `S`.  Then
> `V(S) = ⋃_{p ≠ q ∈ S} closure (VR(p,S)) ∩ J(p,q)`
> `     = ⋃_{p ≠ q ∈ S} closure (VR(p,S)) ∩ closure (VR(q,S))`. 

```lean
theorem lemma3 (hadm : C.Admissible) :
    C.V S = (⋃ p ∈ S, ⋃ q ∈ S.erase p, closure (C.VR p S) ∩ C.J p q) ∧
      C.V S = (⋃ p ∈ S, ⋃ q ∈ S.erase p, closure (C.VR p S) ∩ closure (C.VR q S))
```

## Theorem 4

*Source: `AbstractVoronoi/Paper/Theorem4.lean`*

 **Theorem 4** of Klein–Langetepe–Nilforoushan (2009), stated as a proposition.

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
  theorem of the dependency.  Theorem 4 therefore carries no unproved hypothesis. 

```lean
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
```

 **Theorem 4** of Klein–Langetepe–Nilforoushan (2009).

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
assumption. 

```lean
theorem theorem4 : JordanCurveAccessibility
```

## Lemma 5

*Source: `AbstractVoronoi/Paper/Lemma5.lean`*

 **Lemma 5** (transitivity lemma) of Klein–Langetepe–Nilforoushan (2009).

> Let `p, q, r ∈ S`.  Then `D(p,q) ∩ D(q,r) ⊆ D(p,r)` holds. 

```lean
theorem lemma5 (hadm : C.Admissible) {p q r : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    C.D p q ∩ C.D q r ⊆ C.D p r
```

## Lemma 6

*Source: `AbstractVoronoi/Paper/Lemma6.lean`*

 **Lemma 6** of Klein–Langetepe–Nilforoushan (2009).

> There cannot be four points consecutively visited by `J(p,r)` that belong alternately to
> `D(p,q)` and `D(q,p)`.

Here "consecutively visited" is expressed through a parametrization `g` of the curve
`J(p,r)`: the four points are `g t₁, g t₂, g t₃, g t₄` with `t₁ < t₂ < t₃ < t₄`, and
"alternately" allows both patterns.  As in Subsection 3.1 of the paper, three sites
`p, q, r ∈ S` are involved. 

```lean
theorem lemma6 (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {g : ℝ → Plane} (hg : IsProperLineParam g (C.J p r))
    {t₁ t₂ t₃ t₄ : ℝ} (h12 : t₁ < t₂) (h23 : t₂ < t₃) (h34 : t₃ < t₄) :
    ¬ ((g t₁ ∈ C.D q p ∧ g t₂ ∈ C.D p q ∧ g t₃ ∈ C.D q p ∧ g t₄ ∈ C.D p q) ∨
       (g t₁ ∈ C.D p q ∧ g t₂ ∈ C.D q p ∧ g t₃ ∈ C.D p q ∧ g t₄ ∈ C.D q p))
```

## Lemma 7

*Source: `AbstractVoronoi/Paper/Lemma7.lean`*

 **Lemma 7** (i) of Klein–Langetepe–Nilforoushan (2009).

> If `G⁻, G⁺` are contained in the closure of the same half-plane defined by `J(p,q)`, the
> same holds for `F⁻, F⁺` with respect to `J(p,r)`.

Here `f` parametrizes `J(p,q)` and `g` parametrizes `J(p,r)`, both passing through the
common point `w` at time `0`; `F∓` and `G∓` are the branches of these curves before and
after `w`.  The hypotheses `hnd₃`, `hnd₄` are part of the standing non-degeneracy assumption
of the paper (footnote 8, stated just before the case distinction A, B, C, D): none of the
segments `F⁻, F⁺` is contained in `J(p,r)`.  The remaining two conditions of that footnote
(none of `G⁻, G⁺` is contained in `J(p,q)`) turn out not to be needed. 

```lean
theorem lemma7_touching (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hnd₃ : ¬ BranchBefore f (C.J p r)) (hnd₄ : ¬ BranchAfter f (C.J p r))
    (hG : (BranchBefore g (closure (C.D p q)) ∧ BranchAfter g (closure (C.D p q))) ∨
          (BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D q p)))) :
    (BranchBefore f (closure (C.D p r)) ∧ BranchAfter f (closure (C.D p r))) ∨
      (BranchBefore f (closure (C.D r p)) ∧ BranchAfter f (closure (C.D r p)))
```

 **Lemma 7** (ii) of Klein–Langetepe–Nilforoushan (2009).

> If `F⁻ ⊆ closure (D(p,r))` and `F⁺ ⊆ closure (D(r,p))` then `G⁻ ⊆ closure (D(q,p))` and
> `G⁺ ⊆ closure (D(p,q))`.  The same holds with `+` and `−` reversed.

In other words, if `J(p,q)` crosses `J(p,r)` at `w`, then `J(p,r)` crosses `J(p,q)` at `w`.
The paper fixes which of the two crossing patterns occurs by its orientation convention
("`D(p,r)` lies on the right hand side of `J(p,r)` as `t` tends to `+∞`"); since that
convention is not formalised here, the conclusion is stated in the orientation-free form:
the two branches `G⁻, G⁺` lie in the closures of *different* half-planes of `J(p,q)`, which
is exactly the assertion of the lemma together with its "`+` and `−` reversed" variant.
As in part (i), `hnd₃`, `hnd₄` are the non-degeneracy assumption of footnote 8 of the paper
for the two branches of `J(p,q)`; the corresponding conditions for `J(p,r)` are not needed.

```lean
theorem lemma7_crossing (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) {w : Plane}
    {f g : ℝ → Plane} (hf : IsProperLineParamAt f (C.J p q) w)
    (hg : IsProperLineParamAt g (C.J p r) w)
    (hnd₃ : ¬ BranchBefore f (C.J p r)) (hnd₄ : ¬ BranchAfter f (C.J p r))
    (hF : BranchBefore f (closure (C.D p r)) ∧ BranchAfter f (closure (C.D r p))) :
    (BranchBefore g (closure (C.D q p)) ∧ BranchAfter g (closure (C.D p q))) ∨
      (BranchBefore g (closure (C.D p q)) ∧ BranchAfter g (closure (C.D q p)))
```

## Lemma 8

*Source: `AbstractVoronoi/Paper/Lemma8.lean`*

 **Lemma 8** of Klein–Langetepe–Nilforoushan (2009).

> Let `w` be a point on the boundary of `VR(p, S)`, where `|S| = 3`.  Then there exists an
> arc `α` with endpoint `w` such that `α \ {w} ⊆ VR(p, S)` holds.

The three sites form a subset `S' ⊆ S` of size three, and the Voronoi regions are taken
with respect to `S'`.  The case in which `w` lies on both bisecting curves through `p` is
`lemma8_common_point`; the two cases in which `w` lies on only one of them are settled here
directly from Theorem 4. 

```lean
theorem lemma8 (hadm : C.Admissible) {S' : Finset ι} (hS' : S' ⊆ S) (hcard : S'.card = 3)
    {p : ι} (hp : p ∈ S') {w : Plane} (hw : w ∈ frontier (C.VR p S')) :
    AccessibleFrom (C.VR p S') w
```

## Lemma 9

*Source: `AbstractVoronoi/Paper/Lemma9.lean`*

 **Lemma 9** of Klein–Langetepe–Nilforoushan (2009).

> Let `B` be the set of all points on the boundaries of at least three Voronoi regions in
> some Voronoi diagram `V(S')`, where `S' ⊆ S`.  If `|S| = n ⩾ 3` then `B` is of size at most
> `2·C(n,3)`.

The paper states the bound under the hypothesis `n ⩾ 3`; that hypothesis turns out not to be
needed, since for `|S| < 3` both sides of the inequality are `0`, so it is omitted here. 

```lean
theorem lemma9 (hadm : C.Admissible) :
    C.BSet.Finite ∧ C.BSet.ncard ≤ 2 * (S.card.choose 3)
```

## Theorem 10

*Source: `AbstractVoronoi/Paper/Theorem10.lean`*

 **Theorem 10** of Klein–Langetepe–Nilforoushan (2009).

> The abstract Voronoi diagram `V(S)`, where `|S| = n`, is a finite plane graph of `O(n)`
> edges and vertices.

The plane graph structure is expressed as follows.  The Voronoi diagram is the disjoint
union of its set `B'` of Voronoi vertices (the points lying on at least three region
boundaries) and of its edges, the connected components of `V(S) \ B'`; distinct edges are
disjoint, each edge is connected and contained in a single bisecting curve `J(p,q)`, and
there are only finitely many vertices and edges, at most `2n` of the former and `3n` of the
latter — the assertion "`O(n)` edges and vertices" of the paper.

The hypothesis `n ⩾ 3` used in the paper to split off the degenerate cases is not needed.

Everything in this statement is proved from Lemmas 8 and 9 except the two bounds `2n` and
`3n`, for which the proof below uses Euler's inequality `AVD.EulerSphereInequality` for
plane graphs.  That inequality is the only unproved statement of the development, and it
is the hypothesis `hEuler` of the theorem; the other ingredient of the Euler count, the
degree condition at a Voronoi vertex, is proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).

Sharper bounds that do *not* use Euler's formula, and are therefore proved outright, are
available separately: at most `2·C(n,3)` vertices by Lemma 9
(`AVD.CurveSystem.vertexSet_ncard_le`) and at most `C(n,2)·(2·C(n,3) + 1)` edges
(`AVD.CurveSystem.edgeSet_ncard_le`). 

```lean
theorem theorem10 (hEuler : EulerSphereInequality) (hadm : C.Admissible) :
    C.V S = C.vertexSet S ∪ ⋃₀ C.edgeSet ∧
      Disjoint (C.vertexSet S) (⋃₀ C.edgeSet) ∧
      (∀ e ∈ C.edgeSet, IsConnected e ∧ ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ e ⊆ C.J p q) ∧
      (∀ e ∈ C.edgeSet, ∀ e' ∈ C.edgeSet, e ≠ e' → Disjoint e e') ∧
      (C.vertexSet S).Finite ∧ C.edgeSet.Finite ∧
      (C.vertexSet S).ncard ≤ 2 * S.card ∧ C.edgeSet.ncard ≤ 3 * S.card
```

## The remaining unproved statements

*Source: `AbstractVoronoi/Jordan/PlaneGraph.lean`*

 The **faces** of a plane set `G`: the connected components of the complement of `G`.

For the Voronoi diagram `V(S)` of an admissible curve system these are exactly the non-empty
Voronoi regions (`AVD.CurveSystem.faceSet_V_eq`). 

```lean
def faceSet (G : Set Plane) : Set (Set Plane) :=
  {F | ∃ z ∈ Gᶜ, F = connectedComponentIn Gᶜ z}
```

 `Vtx` and `Edg` form a **finite plane graph**: `Vtx` is a finite set of points of the
plane (the *vertices*), `Edg` is a finite set of pairwise disjoint connected sets (the
*edges*), disjoint from `Vtx`, each of which is an open subarc of a properly embedded line of
the plane, and the ends of an edge — the points of its closure that are not on it — are
vertices.  The union `Vtx ∪ ⋃ Edg` of the graph is required to be closed.

This is the shape of the plane graph produced by Theorem 10 of
Klein–Langetepe–Nilforoushan (2009): the vertices are the points lying on at least three
Voronoi region boundaries, and the edges are the connected components of the rest of the
diagram, each of which is an open piece of a bisecting curve.  Unbounded edges are allowed,
since bisecting curves are unbounded. 

```lean
structure IsFinitePlaneGraph (Vtx : Set Plane) (Edg : Set (Set Plane)) : Prop where
  /-- There are finitely many vertices. -/
  vtx_finite : Vtx.Finite
  /-- There are finitely many edges. -/
  edge_finite : Edg.Finite
  /-- Every edge is connected and non-empty. -/
  edge_isConnected : ∀ e ∈ Edg, IsConnected e
  /-- Distinct edges are disjoint. -/
  edge_disjoint : ∀ e ∈ Edg, ∀ e' ∈ Edg, e ≠ e' → Disjoint e e'
  /-- No edge passes through a vertex. -/
  vtx_disjoint : Disjoint Vtx (⋃₀ Edg)
  /-- Every edge is an open subarc of a properly embedded line of the plane. -/
  edge_isArc : ∀ e ∈ Edg, ∃ (γ : ℝ → Plane) (L : Set Plane) (I : Set ℝ),
    IsProperLineParam γ L ∧ IsOpen I ∧ IsPreconnected I ∧ e = γ '' I
  /-- The ends of an edge are vertices. -/
  edge_ends : ∀ e ∈ Edg, closure e \ e ⊆ Vtx
  /-- The graph is a closed subset of the plane. -/
  isClosed : IsClosed (Vtx ∪ ⋃₀ Edg)
```

 **Euler's formula** for a bounded connected finite plane graph: if the graph
`Vtx ∪ ⋃ Edg` is connected and bounded (so that all of its edges are bounded arcs) and has
finitely many faces, then

`(number of vertices) + (number of faces) = (number of edges) + 2`,

the faces being the connected components of the complement of the graph, the unbounded one
included.

This proposition is *not* proved in this development.  It is stated for reference: it is the
classical form of the statement that the proof of Theorem 10 of
Klein–Langetepe–Nilforoushan (2009) appeals to.  What that proof actually uses is the
consequence `AVD.EulerPlaneBounds` below, which also covers the unbounded edges occurring in
a Voronoi diagram. 

```lean
def EulerFormula : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    IsConnected (Vtx ∪ ⋃₀ Edg) → Bornology.IsBounded (Vtx ∪ ⋃₀ Edg) →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    Vtx.ncard + (faceSet (Vtx ∪ ⋃₀ Edg)).ncard = Edg.ncard + 2
```

 The **counting consequence of Euler's formula** used in the proof of Theorem 10 of
Klein–Langetepe–Nilforoushan (2009): for a finite plane graph with finitely many faces, in
which every vertex lies on the closures of at least three faces, the number of vertices is at
most twice, and the number of edges at most three times, the number of faces.

This is the classical chain: a point lying on the closures of three faces is incident with at
least three edges, so `2·e ⩾ 3·v` by the handshake lemma, while Euler's formula on the sphere
— the plane graph compactified by one point at infinity, which absorbs the ends of the
unbounded edges — gives `v - e + f ⩾ 2 - 1`; eliminating `v` yields `e ⩽ 3f - 3` and
`v ⩽ 2f - 2`.  The bounds are stated with this slack, in the form in which the paper uses
them: with at most `n` faces one gets `O(n)` vertices and edges.

Only the two classical inputs to this chain are taken on faith here, in the form of
`AVD.EulerSphereInput`; the counting itself is proved, in
`AVD.eulerPlaneBounds_of_eulerSphereInput`.  For the Voronoi diagram the first of the two,
the degree condition, is proved (`AVD.CurveSystem.three_le_edges_at_vertex`), so that only
the Euler inequality is left. 

```lean
def EulerPlaneBounds : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    (∀ v ∈ Vtx, 3 ≤ {F ∈ faceSet (Vtx ∪ ⋃₀ Edg) | v ∈ closure F}.ncard) →
    Vtx.ncard ≤ 2 * (faceSet (Vtx ∪ ⋃₀ Edg)).ncard ∧
      Edg.ncard ≤ 3 * (faceSet (Vtx ∪ ⋃₀ Edg)).ncard
```

 The **degree condition** of the Euler count, as a statement about plane graphs: in a
finite plane graph with finitely many faces, a vertex lying on the closures of at least three
faces is an end of at least three edges — three faces meeting at a point must be separated
near it by three different edges.

This proposition is **not proved** in this development for arbitrary plane graphs, and it is
no longer used: the instance of it that the proof of Theorem 10 needs, the one for the
Voronoi diagram of an admissible curve system, is proved
(`AVD.CurveSystem.three_le_edges_at_vertex`).  It is kept here because it is the classical
statement the paper appeals to. 

```lean
def PlaneGraphVertexDegree : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    (∀ v ∈ Vtx, 3 ≤ {F ∈ faceSet (Vtx ∪ ⋃₀ Edg) | v ∈ closure F}.ncard) →
    ∀ v ∈ Vtx, 3 ≤ {e ∈ Edg | v ∈ closure e}.ncard
```

 The **Euler inequality on the sphere**, `e + 1 ⩽ v + f`, for a finite plane graph with
finitely many faces: compactifying the plane by one point at infinity, which absorbs the ends
of the unbounded edges, turns the graph into a graph on the sphere with at most one extra
vertex, for which `v - e + f ⩾ 2`.

This proposition is **not proved** in this development; it is Euler's formula for embedded
plane graphs, which no available library supplies (see `notes/euler-formula-and-counting.md`).
It is the one statement that the proof of `AVD.CurveSystem.theorem10` still takes on faith. 

```lean
def EulerSphereInequality : Prop :=
  ∀ (Vtx : Set Plane) (Edg : Set (Set Plane)), IsFinitePlaneGraph Vtx Edg →
    (faceSet (Vtx ∪ ⋃₀ Edg)).Finite →
    Edg.ncard + 1 ≤ Vtx.ncard + (faceSet (Vtx ∪ ⋃₀ Edg)).ncard
```

*Source: `AbstractVoronoi/AVD/VertexDegree.lean`*

 **If all the edges ending at a point of the diagram lie on a single bisecting curve, then
at most two faces meet there.**

Near `z` the diagram consists of `z` and of the edges having `z` in their closure
(`AVD.CurveSystem.exists_nbhd_V_inter_subset`); if all of these lie on the curve `J(p,q)`,
which passes through `z`, then in a small enough neighbourhood the diagram is a subset of
`J(p,q)`, and the local structure of a Jordan curve — the two connected half-neighbourhoods
supplied by **Theorem 4** — leaves room for at most two faces
(`AVD.faces_at_ncard_le_two_of_local_subset_jordan`). 

```lean
theorem faces_at_le_two_of_edges_subset_J (hadm : C.Admissible) {z : Plane} {p q : ι}
    (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) (hzJ : z ∈ C.J p q)
    (hsub : ∀ e ∈ C.edgeSet, z ∈ closure e → e ⊆ C.J p q) :
    {F ∈ faceSet (C.V S) | z ∈ closure F}.ncard ≤ 2 := by
  -- the two domains of the curve, and their common frontier
  have hf1 : frontier (C.D p q) = C.J p q := frontier_D_eq_J hadm hp hq hpq
  have hf2 : frontier (C.D q p) = C.J p q := by
    rw [frontier_D_eq_J hadm hq hp hpq.symm, C.J_symm hq hp hpq.symm]
  have hunion : C.D p q ∪ C.D q p = (C.J p q)ᶜ := (C.compl_J p hp q hq hpq).symm
  -- a neighbourhood of `z` in which the diagram lies on the curve
  obtain ⟨U₀, hU₀open, hzU₀, -, hU₀sub⟩ :=
    exists_nbhd_V_inter_subset (W := univ) hadm Filter.univ_mem
  have hVU₀ : C.V S ∩ U₀ ⊆ C.J p q := by
    intro x hx
    rcases hU₀sub hx with hx' | ⟨e, he, hxe⟩
    · rw [hx']; exact hzJ
    · exact hsub e he.1 he.2 hxe
  -- shrink it to one of the neighbourhoods supplied by Theorem 4
  obtain ⟨U, hUnhds, hUU₀, hUopen, hc1, hc2, -, -⟩ :=
    jordanCurveLocalStructure (C.J p q) (Or.inr (hadm.A1 p hp q hq hpq))
      (C.D p q) (C.D q p) (C.D_isOpen p hp q hq hpq) (C.D_isOpen q hq p hp hpq.symm)
      (D_isConnected hadm hp hq hpq) (D_isConnected hadm hq hp hpq.symm)
      (C.D_disjoint p hp q hq hpq) hunion hf1 hf2 z hzJ U₀ (hU₀open.mem_nhds hzU₀)
  refine faces_at_ncard_le_two_of_local_subset_jordan isClosed_V hunion hf1 hf2 hUopen
    (mem_of_mem_nhds hUnhds) hc1 hc2 ?_
  exact fun x hx => hVU₀ ⟨hx.1, hUU₀ hx.2⟩
```

 The counting form of `AVD.CurveSystem.exists_two_edges_at_vertex`: at least two edges of
the Voronoi diagram have a given Voronoi vertex in their closure. 

```lean
theorem two_le_edges_at_vertex (hadm : C.Admissible) {z : Plane} (hz : z ∈ C.vertexSet S) :
    2 ≤ {e ∈ C.edgeSet | z ∈ closure e}.ncard := by
  obtain ⟨e₁, he₁, e₂, he₂, hne, hz₁, hz₂, -⟩ := exists_two_edges_at_vertex hadm hz
  have hsub : ({e₁, e₂} : Set (Set Plane)) ⊆ {e ∈ C.edgeSet | z ∈ closure e} := by
    rintro e (rfl | rfl)
    · exact ⟨he₁, hz₁⟩
    · exact ⟨he₂, hz₂⟩
  have hfin : {e ∈ C.edgeSet | z ∈ closure e}.Finite :=
    (edgeSet_finite hadm).subset fun e he => he.1
  calc (2 : ℕ) = ({e₁, e₂} : Set (Set Plane)).ncard := by
        rw [Set.ncard_pair hne]
    _ ≤ _ := Set.ncard_le_ncard hsub hfin
```

 **At least three edges of the Voronoi diagram end at a Voronoi vertex.**

This is the degree condition used by the Euler count in the proof of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009), for the Voronoi diagram of an admissible system of
bisecting curves; the general statement for plane graphs is `AVD.PlaneGraphVertexDegree`.

At least two edges end at a Voronoi vertex `z`
(`AVD.CurveSystem.two_le_edges_at_vertex`).  If there were exactly two, say `e₁` and `e₂`,
then near `z` the diagram would consist of `z` and of those two edges
(`AVD.CurveSystem.exists_nbhd_V_inter_subset`), each of which is, near `z`, a single branch
`γᵢ((0,dᵢ))` of a properly embedded bisecting curve with `γᵢ 0 = z`
(`AVD.CurveSystem.edge_isBranch_at_end`).  The two branches are disjoint, so together with
`z` they form an arc through `z` which, being continuable along the two curves, lies on a
closed Jordan curve (`AVD.exists_closedJordanCurve_two_branches`).  In a small enough
neighbourhood of `z` the diagram is therefore contained in a single Jordan curve, and at most
two faces can have `z` in their closure
(`AVD.faces_at_ncard_le_two_of_local_subset_jordan`) — contradicting the fact that at least
three do (`AVD.CurveSystem.three_le_faces_at_vertex`). 

```lean
theorem three_le_edges_at_vertex (hadm : C.Admissible) {z : Plane} (hz : z ∈ C.vertexSet S) :
    3 ≤ {e ∈ C.edgeSet | z ∈ closure e}.ncard := by
  classical
  by_contra hlt
  push Not at hlt
  have hfin : {e ∈ C.edgeSet | z ∈ closure e}.Finite :=
    (edgeSet_finite hadm).subset fun e he => he.1
  obtain ⟨e₁, he₁, e₂, he₂, hne, hzc₁, hzc₂, -⟩ := exists_two_edges_at_vertex hadm hz
  -- the edges ending at `z` are exactly `e₁` and `e₂`
  have hsub : ({e₁, e₂} : Set (Set Plane)) ⊆ {e ∈ C.edgeSet | z ∈ closure e} := by
    rintro e (rfl | rfl)
    · exact ⟨he₁, hzc₁⟩
    · exact ⟨he₂, hzc₂⟩
  have hpair : ({e₁, e₂} : Set (Set Plane)) = {e ∈ C.edgeSet | z ∈ closure e} := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [Set.ncard_pair hne]
    omega
  -- `z` is an end of each of the two edges, along a single branch of its bisecting curve
  have hgraph : IsFinitePlaneGraph (C.vertexSet S) C.edgeSet := isFinitePlaneGraph hadm
  have hznot : ∀ e ∈ C.edgeSet, z ∉ e := fun e he hze =>
    (Set.disjoint_left.1 hgraph.vtx_disjoint) hz ⟨e, he, hze⟩
  obtain ⟨γ₁, L₁, hγ₁, hγ₁0, -, ⟨b₁, hb₁, hbr₁⟩, hnear₁⟩ :=
    edge_isBranch_at_end hadm he₁ ⟨hzc₁, hznot e₁ he₁⟩
  obtain ⟨γ₂, L₂, hγ₂, hγ₂0, -, ⟨b₂, hb₂, hbr₂⟩, hnear₂⟩ :=
    edge_isBranch_at_end hadm he₂ ⟨hzc₂, hznot e₂ he₂⟩
  set d₁ : ℝ := b₁ / 4 with hd₁def
  set c₁ : ℝ := b₁ / 2 with hc₁def
  set d₂ : ℝ := b₂ / 4 with hd₂def
  set c₂ : ℝ := b₂ / 2 with hc₂def
  have hd₁ : 0 < d₁ := by rw [hd₁def]; linarith
  have hd₂ : 0 < d₂ := by rw [hd₂def]; linarith
  have hdc₁ : d₁ < c₁ := by rw [hd₁def, hc₁def]; linarith
  have hdc₂ : d₂ < c₂ := by rw [hd₂def, hc₂def]; linarith
  -- the longer branches still lie on the edges, which are disjoint
  have hbc₁ : γ₁ '' Ioc 0 c₁ ⊆ e₁ := by
    refine subset_trans (Set.image_mono ?_) hbr₁
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 (by rw [hc₁def]; linarith)⟩
  have hbc₂ : γ₂ '' Ioc 0 c₂ ⊆ e₂ := by
    refine subset_trans (Set.image_mono ?_) hbr₂
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 (by rw [hc₂def]; linarith)⟩
  have hdisjbr : Disjoint (γ₁ '' Ioc 0 c₁) (γ₂ '' Ioc 0 c₂) :=
    (hgraph.edge_disjoint e₁ he₁ e₂ he₂ hne).mono hbc₁ hbc₂
  -- the two branches, joined at `z`, lie on a closed Jordan curve
  obtain ⟨Jc, hJc, hJsub⟩ :=
    exists_closedJordanCurve_two_branches hγ₁ hγ₂ (hγ₁0.trans hγ₂0.symm) hd₁ hdc₁ hd₂ hdc₂
      hdisjbr
  have hzJ : z ∈ Jc := hJsub (Or.inl ⟨0, ⟨le_refl 0, hd₁.le⟩, hγ₁0⟩)
  obtain ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisjD, hunion, hf1, hf2, -⟩ :=
    hJc.exists_separation_frontier_eq
  -- a neighbourhood of `z` in which the diagram lies on that curve
  obtain ⟨r₁, hr₁, hnb₁⟩ := hnear₁ d₁ hd₁
  obtain ⟨r₂, hr₂, hnb₂⟩ := hnear₂ d₂ hd₂
  obtain ⟨U₀, hU₀open, hzU₀, -, hU₀sub⟩ :=
    exists_nbhd_V_inter_subset (W := univ) hadm Filter.univ_mem
  set N : Set Plane := U₀ ∩ (ball z r₁ ∩ ball z r₂) with hNdef
  have hNopen : IsOpen N := hU₀open.inter (isOpen_ball.inter isOpen_ball)
  have hzN : z ∈ N := ⟨hzU₀, mem_ball_self hr₁, mem_ball_self hr₂⟩
  have hVN : C.V S ∩ N ⊆ Jc := by
    rintro x ⟨hxV, hxU₀, hxr₁, hxr₂⟩
    rcases hU₀sub ⟨hxV, hxU₀⟩ with hx | ⟨e, he, hxe⟩
    · rw [Set.mem_singleton_iff.1 hx]; exact hzJ
    · rw [← hpair] at he
      rcases he with rfl | rfl
      · exact hJsub (Or.inl (Set.image_mono Ioo_subset_Icc_self (hnb₁ ⟨hxe, hxr₁⟩)))
      · exact hJsub (Or.inr (Set.image_mono Ioo_subset_Icc_self (hnb₂ ⟨hxe, hxr₂⟩)))
  -- the local structure of that curve at `z` bounds the number of faces meeting `z`
  obtain ⟨U, hUnhds, hUN, hUopen, hcc1, hcc2, -, -⟩ :=
    jordanCurveLocalStructure Jc (Or.inl hJc) D₁ D₂ h1o h2o h1c h2c hdisjD hunion hf1 hf2 z
      hzJ N (hNopen.mem_nhds hzN)
  have hle2 : {F ∈ faceSet (C.V S) | z ∈ closure F}.ncard ≤ 2 :=
    faces_at_ncard_le_two_of_local_subset_jordan isClosed_V hunion hf1 hf2 hUopen
      (mem_of_mem_nhds hUnhds) hcc1 hcc2 (fun x hx => hVN ⟨hx.1, hUN hx.2⟩)
  have h3 := three_le_faces_at_vertex hadm hz
  omega
```
