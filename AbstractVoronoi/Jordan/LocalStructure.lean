import AbstractVoronoi.Jordan.SphereTransfer
import AbstractVoronoi.Jordan.LocalConnectivity
import AbstractVoronoi.Jordan.SchoenfliesUnbounded

/-!
# The local structure of a Jordan curve: the statements of Theorem 4

This file states, for the plane curves of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

the three `Prop`-valued forms of the *local* part of **Theorem 4** that the development
distinguishes, in decreasing strength:

* `AVD.JordanCurveLocalAccessibility` — the local part of Theorem 4 as the paper states it
  (the small neighbourhood `U` of a point of the curve is bounded by a closed Jordan curve).
  It is *proved* in `AbstractVoronoi.Paper.Theorem4`;
* `AVD.JordanCurveLocalStructure` — the same without the clause about the boundary of `U`.
  Every use of Theorem 4 in the proofs of Lemmas 5 to 9 and of Theorem 10 goes through this
  statement, which is *proved* here;
* `AVD.JordanCurveLocalConnectedness` — the local connectedness of the two complementary
  domains at the points of the curve.  This is the Jordan–Schönflies content of Theorem 4,
  in the weakest form in which the paper uses it; it is *proved*
  (`AVD.jordanCurveLocalConnectedness`) from the Jordan–Schönflies theorem of the
  dependency, in `AbstractVoronoi.Jordan.SchoenfliesClosed` (closed Jordan curves) and
  `AbstractVoronoi.Jordan.SchoenfliesUnbounded` (the unbounded curves of axiom `A₁`).

The literal statement of Theorem 4, `AVD.JordanCurveAccessibility`, and its proof are in
`AbstractVoronoi.Paper.Theorem4`; its *global* part is proved, with no assumption, in
`AbstractVoronoi.Jordan.Schoenflies` (closed Jordan curves) and
`AbstractVoronoi.Jordan.SphereTransfer` (the unbounded curves of axiom `A₁`).
-/


noncomputable section

open Set Topology

namespace AVD

/-! ## The local part of Theorem 4

The two kinds of Jordan curves — closed ones and the unbounded ones of axiom `A₁` — are
defined in `AbstractVoronoi.Jordan.Sphere`. -/

/-- The **local** part of Theorem 4 of Klein–Langetepe–Nilforoushan (2009), isolated as a
statement of its own:

> For each point `z ∈ C` there exists a neighbourhood `U` whose boundary is homeomorphic to
> a circle, such that `U \ C` consists of exactly two connected components.  Point `z` is
> accessible from each domain `U ∩ Dᵢ`, that is, for each `p ∈ U ∩ Dᵢ` there exists an arc
> `α` from `p` to `z` such that `α` minus its endpoint `z` belongs to `U ∩ Dᵢ`.

Here the two complementary domains `D₁, D₂` of the curve are given as data, subject to the
conclusions of the global part of Theorem 4, which is proved in this development
(`AVD.IsClosedJordanCurve.exists_separation_frontier_eq` and
`AVD.IsUnboundedJordanCurve.exists_separation_frontier_eq`).  As in
`AVD.JordanCurveAccessibility`, "there exists a neighbourhood `U`" is strengthened to
"arbitrarily small such neighbourhoods exist", which is how the paper uses the theorem.

This statement is the Jordan–Schönflies content of Theorem 4 (it says that `C` is locally
flat at each of its points); it is **proved** in this development, as
`AVD.jordanCurveLocalAccessibility`, from the local connectedness of the two complementary
domains (`AVD.jordanCurveLocalConnectedness`). -/
def JordanCurveLocalAccessibility : Prop :=
  ∀ C : Set Plane, IsJordanCurve C → ∀ D₁ D₂ : Set Plane,
    IsOpen D₁ → IsOpen D₂ → IsConnected D₁ → IsConnected D₂ → Disjoint D₁ D₂ →
    D₁ ∪ D₂ = Cᶜ → frontier D₁ = C → frontier D₂ = C →
    ∀ z ∈ C, ∀ V ∈ 𝓝 z, ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧
      IsClosedJordanCurve (frontier U) ∧
      IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
      (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
      (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z)

/-- The part of `AVD.JordanCurveLocalAccessibility` that is actually used in the rest of the
development, that is, everywhere Theorem 4 of Klein–Langetepe–Nilforoushan (2009) is applied
in the proofs of Lemmas 5 to 9 and of Theorem 10:

> For each point `z ∈ C` there exists a neighbourhood `U` [...] such that `U \ C` consists of
> exactly two connected components.  Point `z` is accessible from each domain `U ∩ Dᵢ`.

It is `AVD.JordanCurveLocalAccessibility` with the clause "whose boundary is homeomorphic to
a circle" dropped.  That clause is part of the statement of Theorem 4, and is therefore kept
in `AVD.JordanCurveLocalAccessibility` and in `AVD.theorem4`, but it is used nowhere else in
the paper; isolating the remainder records that everything the paper proves after Theorem 4
depends only on this weaker statement. -/
def JordanCurveLocalStructure : Prop :=
  ∀ C : Set Plane, IsJordanCurve C → ∀ D₁ D₂ : Set Plane,
    IsOpen D₁ → IsOpen D₂ → IsConnected D₁ → IsConnected D₂ → Disjoint D₁ D₂ →
    D₁ ∪ D₂ = Cᶜ → frontier D₁ = C → frontier D₂ = C →
    ∀ z ∈ C, ∀ V ∈ 𝓝 z, ∃ U : Set Plane, U ∈ 𝓝 z ∧ U ⊆ V ∧ IsOpen U ∧
      IsConnected (U ∩ D₁) ∧ IsConnected (U ∩ D₂) ∧
      (∀ x ∈ U ∩ D₁, AccessibleWithin (U ∩ D₁) x z) ∧
      (∀ x ∈ U ∩ D₂, AccessibleWithin (U ∩ D₂) x z)

/-- The **local connectedness** of the complementary domains of a Jordan curve at the points
of the curve, stated as a proposition.

For every Jordan curve `C` with complementary domains `D₁, D₂` (as supplied by the proved
global part of Theorem 4 of Klein–Langetepe–Nilforoushan (2009)) and every point `z ∈ C`,
the domain `D₁` is locally connected at `z` in the uniform sense of
`AVD.LocallyConnectedAt`: any two points of `D₁` close enough to `z` can be joined by a path
inside `D₁` staying close to `z`.  By the symmetry of the hypotheses in `D₁` and `D₂` the
same then holds for `D₂`.

This is a *formally weaker* statement than the local part of Theorem 4: it is implied by
`AVD.JordanCurveLocalAccessibility` (see `AVD.jordanCurveLocalConnectedness_of_accessibility`)
and, conversely, it implies everything the paper uses after Theorem 4, namely
`AVD.JordanCurveLocalStructure` (see `AVD.jordanCurveLocalStructure`).  It is the
Jordan–Schönflies content of Theorem 4, in the weakest form in which it is needed, and it is
proved in this development from the Jordan–Schönflies theorem of the dependency. -/
def JordanCurveLocalConnectedness : Prop :=
  ∀ C : Set Plane, IsJordanCurve C → ∀ D₁ D₂ : Set Plane,
    IsOpen D₁ → IsOpen D₂ → IsConnected D₁ → IsConnected D₂ → Disjoint D₁ D₂ →
    D₁ ∪ D₂ = Cᶜ → frontier D₁ = C → frontier D₂ = C →
    ∀ z ∈ C, LocallyConnectedAt D₁ z

/-- The local connectedness of the complementary domains of a Jordan curve at the points of
the curve, `AVD.JordanCurveLocalConnectedness`: the Jordan–Schönflies content of Theorem 4 of
Klein–Langetepe–Nilforoushan (2009), in the weakest form in which the paper uses it.  Every
application of Theorem 4 in the proofs of Lemmas 5 to 9 and of Theorem 10 goes through this
statement, via `AVD.jordanCurveLocalStructure`.

It is **proved** from the Jordan–Schönflies theorem of the dependency: for a closed Jordan
curve it is `AVD.IsClosedJordanCurve.locallyConnectedAt` (carry the curve onto the boundary
of a square by a homeomorphism of the plane, and read off the local connectedness of the two
explicit complementary domains of that square), and for the unbounded curves of axiom `A₁` it
is `AVD.IsUnboundedJordanCurve.locallyConnectedAt` (the same statement, transported through a
chart of the sphere). -/
theorem jordanCurveLocalConnectedness : JordanCurveLocalConnectedness := by
  intro C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion _ _ z hz
  rcases hC with hC | hC
  · exact hC.locallyConnectedAt h1c h2c hunion hz
  · exact hC.locallyConnectedAt h1o h2o h1c h2c hdisj hunion hz

/-- The local part of Theorem 4 of Klein–Langetepe–Nilforoushan (2009) implies the local
connectedness of the complementary domains at the points of the curve: a neighbourhood `U`
of `z` with `U ∩ D₁` connected is, `D₁` being open, path-connected, which is exactly the
required joining property.  This records that `AVD.JordanCurveLocalConnectedness` is a
weaker hypothesis than `AVD.JordanCurveLocalAccessibility`. -/
theorem jordanCurveLocalConnectedness_of_accessibility
    (h : JordanCurveLocalAccessibility) : JordanCurveLocalConnectedness := by
  intro C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 z hz
  refine locallyConnectedAt_of_small_connected h1o ?_
  intro V hV
  obtain ⟨U, hUnhds, hUV, hUopen, -, hc1, -, -, -⟩ :=
    h C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 z hz V hV
  exact ⟨U, hUnhds, hUV, hUopen, hc1⟩

/-- The local structure of a Jordan curve at one of its points, in the weaker form
`AVD.JordanCurveLocalStructure` in which it is used after Theorem 4 of
Klein–Langetepe–Nilforoushan (2009).  Every later use of Theorem 4 in this development goes
through this statement.

It is *proved* here from the local connectedness of the two complementary domains at the
points of the curve (`AVD.jordanCurveLocalConnectedness`): each domain `Dᵢ` contains, near
`z`, an open connected set `Vᵢ` which swallows all the points of `Dᵢ` close enough to `z` and
from every point of which `z` is accessible (`AVD.exists_locally_connected_nbhd`, whose
access arcs come from the construction `AVD.exists_arc_to_limit`); the neighbourhood `U` of
the statement is then `V₁ ∪ V₂` together with the points of the curve close to `z`. -/
theorem jordanCurveLocalStructure : JordanCurveLocalStructure := by
  intro C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 z hz V hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  -- the two domains do not contain `z`, which lies on their common frontier
  have hz1 : z ∈ frontier D₁ := by rw [hf1]; exact hz
  have hz2 : z ∈ frontier D₂ := by rw [hf2]; exact hz
  have hzD1 : z ∉ D₁ := by
    have h := hz1
    rw [frontier, h1o.interior_eq] at h
    exact h.2
  have hzD2 : z ∉ D₂ := by
    have h := hz2
    rw [frontier, h2o.interior_eq] at h
    exact h.2
  have hzc1 : z ∈ closure D₁ := (frontier_subset_closure hz1)
  have hzc2 : z ∈ closure D₂ := (frontier_subset_closure hz2)
  -- the local connectedness of each domain at `z`
  have hlc1 : LocallyConnectedAt D₁ z :=
    jordanCurveLocalConnectedness C hC D₁ D₂ h1o h2o h1c h2c hdisj hunion hf1 hf2 z hz
  have hlc2 : LocallyConnectedAt D₂ z :=
    jordanCurveLocalConnectedness C hC D₂ D₁ h2o h1o h2c h1c hdisj.symm
      (by rw [union_comm]; exact hunion) hf2 hf1 z hz
  obtain ⟨V₁, δ₁, hV₁open, hV₁conn, hV₁ne, hV₁D, hV₁ball, hδ₁, hδ₁ε, hδ₁sub, hacc₁⟩ :=
    exists_locally_connected_nbhd h1o hzD1 hzc1 hlc1 hε
  obtain ⟨V₂, δ₂, hV₂open, hV₂conn, hV₂ne, hV₂D, hV₂ball, hδ₂, hδ₂ε, hδ₂sub, hacc₂⟩ :=
    exists_locally_connected_nbhd h2o hzD2 hzc2 hlc2 hε
  set δ := min δ₁ δ₂ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  set U : Set Plane := V₁ ∪ V₂ ∪ (C ∩ Metric.ball z δ) with hUdef
  -- the points of the plane close to `z` are on the curve or in one of the `Vᵢ`
  have hnear : ∀ w ∈ Metric.ball z δ, w ∈ U := by
    intro w hw
    by_cases hwC : w ∈ C
    · exact Or.inr ⟨hwC, hw⟩
    · have hwc : w ∈ D₁ ∪ D₂ := by rw [hunion]; exact hwC
      rcases hwc with hw1 | hw2
      · exact Or.inl (Or.inl (hδ₁sub ⟨hw1, Metric.ball_subset_ball (min_le_left δ₁ δ₂) hw⟩))
      · exact Or.inl (Or.inr (hδ₂sub ⟨hw2, Metric.ball_subset_ball (min_le_right δ₁ δ₂) hw⟩))
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    rintro y (hy | hy)
    · rcases hy with hy | hy
      · exact ⟨V₁, fun w hw => Or.inl (Or.inl hw), hV₁open, hy⟩
      · exact ⟨V₂, fun w hw => Or.inl (Or.inr hw), hV₂open, hy⟩
    · exact ⟨Metric.ball z δ, hnear, Metric.isOpen_ball, hy.2⟩
  have hzU : z ∈ U := Or.inr ⟨hz, Metric.mem_ball_self hδ⟩
  -- the trace of `U` on each domain is the corresponding `Vᵢ`
  have hU1 : U ∩ D₁ = V₁ := by
    apply Subset.antisymm
    · rintro w ⟨hwU, hw1⟩
      rcases hwU with (hw | hw) | hw
      · exact hw
      · exact absurd (Set.disjoint_left.1 hdisj hw1 (hV₂D hw)) (fun h => h)
      · exfalso
        have : w ∈ Cᶜ := by rw [← hunion]; exact Or.inl hw1
        exact this hw.1
    · exact fun w hw => ⟨Or.inl (Or.inl hw), hV₁D hw⟩
  have hU2 : U ∩ D₂ = V₂ := by
    apply Subset.antisymm
    · rintro w ⟨hwU, hw2⟩
      rcases hwU with (hw | hw) | hw
      · exact absurd (Set.disjoint_left.1 hdisj (hV₁D hw) hw2) (fun h => h)
      · exact hw
      · exfalso
        have : w ∈ Cᶜ := by rw [← hunion]; exact Or.inr hw2
        exact this hw.1
    · exact fun w hw => ⟨Or.inl (Or.inr hw), hV₂D hw⟩
  refine ⟨U, hUopen.mem_nhds hzU, ?_, hUopen, ?_, ?_, ?_, ?_⟩
  · -- `U` is contained in the prescribed neighbourhood
    rintro w (hw | hw)
    · rcases hw with hw | hw
      · exact hεV (hV₁ball hw)
      · exact hεV (hV₂ball hw)
    · exact hεV (Metric.ball_subset_ball (le_trans (min_le_left δ₁ δ₂) hδ₁ε) hw.2)
  · rw [hU1]; exact ⟨hV₁ne, hV₁conn⟩
  · rw [hU2]; exact ⟨hV₂ne, hV₂conn⟩
  · intro x hx
    rw [hU1] at hx ⊢
    exact hacc₁ x hx
  · intro x hx
    rw [hU2] at hx ⊢
    exact hacc₂ x hx

end AVD
