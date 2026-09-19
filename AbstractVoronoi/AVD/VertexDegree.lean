import AbstractVoronoi.AVD.Faces
import AbstractVoronoi.Jordan.LocalFaces
import AbstractVoronoi.Jordan.ProperLocal
import AbstractVoronoi.Jordan.ArcCompletion

/-!
# How many edges meet at a Voronoi vertex

The Euler count in the proof of **Theorem 10** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

uses the classical fact that a vertex of a plane graph lying on the closures of at least
three faces is an end of at least three edges.  For the Voronoi diagram the hypothesis is
proved (`AVD.CurveSystem.three_le_faces_at_vertex`: a Voronoi vertex lies on the closures of
at least three Voronoi regions, and the regions are the faces), and this file proves the
conclusion — **at least three edges end at every Voronoi vertex**
(`AVD.CurveSystem.three_le_edges_at_vertex`) — by inspecting the diagram in a small
neighbourhood of a vertex.

The main results are

* `AVD.CurveSystem.exists_nbhd_V_inter_subset` — near a point `z` of the diagram, the diagram
  consists of `z` itself and of the edges having `z` in their closure: all other vertices and
  all other edges stay at a positive distance;
* `AVD.CurveSystem.faces_at_le_two_of_edges_subset_J` — if all the edges ending at `z` lie on
  one and the same bisecting curve `J(p,q)`, then at most two faces of the diagram have `z`
  in their closure.  This is `AVD.faces_at_ncard_le_two_of_local_subset_jordan` applied to the
  diagram, the curve `J(p,q)` and one of the neighbourhoods supplied by Theorem 4;
* `AVD.CurveSystem.not_edges_at_vertex_subset_J` — consequently the edges ending at a Voronoi
  vertex never all lie on a single bisecting curve, since three faces meet there;
* `AVD.CurveSystem.two_le_edges_at_vertex` — hence **at least two edges end at a Voronoi
  vertex**, and they lie on at least two different bisecting curves
  (`AVD.CurveSystem.exists_two_edges_at_vertex`);
* `AVD.CurveSystem.edge_isBranch_at_end` — near one of its ends, an edge is a **single
  branch** `γ '' (0, δ)` of a proper parametrization `γ` of the bisecting curve carrying it,
  with `γ 0` the end in question;
* `AVD.CurveSystem.three_le_edges_at_vertex` — **at least three edges end at a Voronoi
  vertex**, the degree condition itself.  If only two ended at `z`, then by the two previous
  items the diagram near `z` would be an arc, formed by one branch of each of the two curves
  carrying the two edges; such an arc lies on a closed Jordan curve
  (`AVD.exists_closedJordanCurve_two_branches`), so again at most two faces could meet at
  `z`, contradicting `AVD.CurveSystem.three_le_faces_at_vertex`.

See `notes/euler-formula-and-counting.md` for how this fits into the Euler count.
-/

noncomputable section

open Set Topology Metric

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- **The diagram near one of its points consists of that point and of the edges ending
there.**  All the other Voronoi vertices, and all the edges that do not have `z` in their
closure, stay at a positive distance from `z`, because there are finitely many of each.  The
neighbourhood can be taken inside any prescribed neighbourhood `W` of `z`. -/
theorem exists_nbhd_V_inter_subset (hadm : C.Admissible) {z : Plane} {W : Set Plane}
    (hW : W ∈ 𝓝 z) :
    ∃ U : Set Plane, IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      C.V S ∩ U ⊆ {z} ∪ ⋃₀ {e ∈ C.edgeSet | z ∈ closure e} := by
  classical
  -- the closed set formed by the other vertices and the closures of the other edges
  set Bad : Set Plane :=
    (C.vertexSet S \ {z}) ∪ ⋃ e ∈ {e ∈ C.edgeSet | z ∉ closure e}, closure e with hBad
  have hvtxfin : (C.vertexSet S).Finite := vertexSet_finite hadm
  have hedgefin : C.edgeSet.Finite := edgeSet_finite hadm
  have hBadClosed : IsClosed Bad := by
    refine IsClosed.union ((hvtxfin.subset (by intro x hx; exact hx.1)).isClosed) ?_
    exact Set.Finite.isClosed_biUnion (hedgefin.subset fun e he => he.1)
      fun e _ => isClosed_closure
  have hzBad : z ∉ Bad := by
    rintro (⟨-, hz2⟩ | hz2)
    · exact hz2 rfl
    · obtain ⟨e, he, hze⟩ := mem_iUnion₂.1 hz2
      exact he.2 hze
  obtain ⟨W', hW'open, hzW', hW'W⟩ : ∃ W', IsOpen W' ∧ z ∈ W' ∧ W' ⊆ W := by
    obtain ⟨t, hts, htopen, hzt⟩ := _root_.mem_nhds_iff.1 hW
    exact ⟨t, htopen, hzt, hts⟩
  refine ⟨W' ∩ Badᶜ, hW'open.inter hBadClosed.isOpen_compl, ⟨hzW', hzBad⟩,
    fun x hx => hW'W hx.1, ?_⟩
  rintro x ⟨hxV, hxW', hxBad⟩
  rw [V_eq_vertexSet_union_edges] at hxV
  rcases hxV with hxv | ⟨e, he, hxe⟩
  · -- `x` is a vertex, hence `x = z`
    left
    by_contra hne
    exact hxBad (Or.inl ⟨hxv, hne⟩)
  · -- `x` lies on an edge, which must have `z` in its closure
    right
    by_cases hz : z ∈ closure e
    · exact ⟨e, ⟨he, hz⟩, hxe⟩
    · exact absurd (Or.inr (mem_iUnion₂.2 ⟨e, ⟨he, hz⟩, subset_closure hxe⟩)) hxBad

/-- A point lying in the closures of the Voronoi regions of two distinct sites lies on the
bisecting curve of those two sites. -/
theorem mem_J_of_mem_closure_two (hadm : C.Admissible) {p q : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) {z : Plane} (hzp : z ∈ closure (C.VR p S)) (hzq : z ∈ closure (C.VR q S)) :
    z ∈ C.J p q := by
  have h1 : z ∈ closure (C.D p q) :=
    closure_mono (fun y hy => VR_subset_D (Finset.mem_erase.2 ⟨hpq.symm, hq⟩) hy) hzp
  have h2 : z ∈ closure (C.D q p) :=
    closure_mono (fun y hy => VR_subset_D (Finset.mem_erase.2 ⟨hpq, hp⟩) hy) hzq
  rw [closure_D_eq hadm hp hq hpq] at h1
  rw [closure_D_eq hadm hq hp hpq.symm] at h2
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd h2 (Set.disjoint_left.1 (C.D_disjoint p hp q hq hpq) h1)
    · exact absurd h1 (notMem_D_of_mem_J hq hp hpq.symm h2).2
  · exact h1

/-- A Voronoi vertex lies on at least one bisecting curve: it is on the closures of the
regions of three distinct sites, and therefore on the bisecting curves of each pair of
them. -/
theorem exists_J_of_mem_vertexSet (hadm : C.Admissible) {z : Plane}
    (hz : z ∈ C.vertexSet S) : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ z ∈ C.J p q := by
  obtain ⟨p, hp, q, hq, -, -, hpq, -, -, hzp, hzq, -⟩ := hz
  exact ⟨p, hp, q, hq, hpq, mem_J_of_mem_closure_two hadm hp hq hpq
    (frontier_subset_closure hzp) (frontier_subset_closure hzq)⟩

/-- **If all the edges ending at a point of the diagram lie on a single bisecting curve, then
at most two faces meet there.**

Near `z` the diagram consists of `z` and of the edges having `z` in their closure
(`AVD.CurveSystem.exists_nbhd_V_inter_subset`); if all of these lie on the curve `J(p,q)`,
which passes through `z`, then in a small enough neighbourhood the diagram is a subset of
`J(p,q)`, and the local structure of a Jordan curve — the two connected half-neighbourhoods
supplied by **Theorem 4** — leaves room for at most two faces
(`AVD.faces_at_ncard_le_two_of_local_subset_jordan`). -/
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

/-- **The edges ending at a Voronoi vertex do not all lie on a single bisecting curve.**

A Voronoi vertex lies on the closures of at least three faces
(`AVD.CurveSystem.three_le_faces_at_vertex`), while a point at which the diagram is locally
contained in a single bisecting curve lies on the closures of at most two
(`AVD.CurveSystem.faces_at_le_two_of_edges_subset_J`). -/
theorem not_edges_at_vertex_subset_J (hadm : C.Admissible) {z : Plane}
    (hz : z ∈ C.vertexSet S) {p q : ι} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ¬ ∀ e ∈ C.edgeSet, z ∈ closure e → e ⊆ C.J p q := by
  intro hsub
  have hthree : 3 ≤ {F ∈ faceSet (C.V S) | z ∈ closure F}.ncard :=
    three_le_faces_at_vertex hadm hz
  by_cases hzJ : z ∈ C.J p q
  · have := faces_at_le_two_of_edges_subset_J hadm hp hq hpq hzJ hsub
    omega
  · -- no edge can end at `z`, and some bisecting curve passes through `z`
    have hnone : ∀ e ∈ C.edgeSet, z ∉ closure e := by
      intro e he hze
      have hJclosed : IsClosed (C.J p q) := by
        rw [← frontier_D_eq_J hadm hp hq hpq]; exact isClosed_frontier
      exact hzJ ((closure_minimal (hsub e he hze) hJclosed) hze)
    obtain ⟨a, ha, b, hb, hab, hzab⟩ := exists_J_of_mem_vertexSet hadm hz
    have := faces_at_le_two_of_edges_subset_J hadm ha hb hab hzab
      (fun e he hze => absurd hze (hnone e he))
    omega

/-- **At least two edges end at a Voronoi vertex, and they lie on two different bisecting
curves.**

This is the part of the degree condition of the Euler count in the proof of **Theorem 10** of
Klein–Langetepe–Nilforoushan (2009) that is proved here: the classical statement is that at
least three edges end at a vertex. -/
theorem exists_two_edges_at_vertex (hadm : C.Admissible) {z : Plane}
    (hz : z ∈ C.vertexSet S) :
    ∃ e₁ ∈ C.edgeSet, ∃ e₂ ∈ C.edgeSet, e₁ ≠ e₂ ∧ z ∈ closure e₁ ∧ z ∈ closure e₂ ∧
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ e₁ ⊆ C.J p q ∧ ¬ e₂ ⊆ C.J p q := by
  classical
  -- some edge ends at `z`
  obtain ⟨a, ha, b, hb, hab, hzab⟩ := exists_J_of_mem_vertexSet hadm hz
  have hsome : ∃ e ∈ C.edgeSet, z ∈ closure e := by
    by_contra hnone
    exact not_edges_at_vertex_subset_J hadm hz ha hb hab
      (fun e he hze => absurd ⟨e, he, hze⟩ hnone)
  obtain ⟨e₁, he₁, hze₁⟩ := hsome
  -- it lies on a bisecting curve, and some other edge ending at `z` does not
  obtain ⟨z₁, hz₁, rfl⟩ := he₁
  obtain ⟨p, hp, q, hq, hpq, hsub⟩ := connectedComponentIn_subset_BPair hadm hz₁
  have he₁J : connectedComponentIn (C.V S \ C.vertexSet S) z₁ ⊆ C.J p q :=
    hsub.trans (BPair_subset_J hp hq hpq)
  obtain ⟨e₂, he₂, hze₂, hne⟩ : ∃ e ∈ C.edgeSet, z ∈ closure e ∧ ¬ e ⊆ C.J p q := by
    by_contra hall
    exact not_edges_at_vertex_subset_J hadm hz hp hq hpq
      (fun e he hze => not_not.1 fun hns => hall ⟨e, he, hze, hns⟩)
  exact ⟨connectedComponentIn (C.V S \ C.vertexSet S) z₁, ⟨z₁, hz₁, rfl⟩, e₂, he₂,
    fun h => hne (h ▸ he₁J), hze₁, hze₂, p, hp, q, hq, hpq, he₁J, hne⟩


/-- **Near one of its ends, an edge of the Voronoi diagram is a single branch of the
bisecting curve carrying it.**

An edge is an open subarc `γ₀ '' I` of a properly embedded bisecting curve
(`AVD.CurveSystem.edge_isSubarc_and_ends`), and a point `z` of its closure which is not on it
is the image `γ₀ a` of a frontier parameter `a` of `I`; the interval `I` then lies entirely on
one side of `a`.  Reparametrizing so that `z` corresponds to the parameter `0` and that side
to the positive parameters, one gets a proper parametrization `γ` with `γ 0 = z` such that

* an initial branch `γ '' (0, b)` with `b > 0` is contained in the edge, and
* for every `δ > 0`, a small enough ball around `z` meets the edge only inside the branch
  `γ '' (0, δ)`.

This is the first ingredient of the configuration that the degree condition of the Euler
count still leaves open (two edges ending at a vertex and lying on two different bisecting
curves); see section 5 of `notes/euler-formula-and-counting.md`. -/
theorem edge_isBranch_at_end (hadm : C.Admissible) {e : Set Plane} (he : e ∈ C.edgeSet)
    {z : Plane} (hz : z ∈ closure e \ e) :
    ∃ (γ : ℝ → Plane) (L : Set Plane), IsProperLineParam γ L ∧ γ 0 = z ∧ e ⊆ L ∧
      (∃ b > 0, γ '' Ioo 0 b ⊆ e) ∧
      ∀ δ > 0, ∃ r > 0, e ∩ ball z r ⊆ γ '' Ioo 0 δ := by
  obtain ⟨γ₀, L, I, hγ₀, hIopen, hIconn, rfl⟩ := (isFinitePlaneGraph hadm).edge_isArc e he
  obtain ⟨hcont, hinj, hrange, hproper⟩ := id hγ₀
  have hproperMap : IsProperMap γ₀ := isProperMap_iff_isCompact_preimage.2 ⟨hcont, hproper⟩
  have hclosure : closure (γ₀ '' I) = γ₀ '' closure I := by
    refine Subset.antisymm (closure_minimal (image_mono subset_closure)
      (hproperMap.isClosedMap _ isClosed_closure)) ?_
    exact image_closure_subset_closure_image hcont
  -- the parameter of `z`
  rw [hclosure] at hz
  obtain ⟨⟨a, hacl, rfl⟩, hznot⟩ := hz
  have haI : a ∉ I := fun h => hznot ⟨a, h, rfl⟩
  have hord : I.OrdConnected := hIconn.ordConnected
  have hne : I.Nonempty := by
    rcases I.eq_empty_or_nonempty with rfl | h
    · rw [closure_empty] at hacl; exact absurd hacl (notMem_empty a)
    · exact h
  -- the interval lies on one side of `a`
  have hside : (∀ s ∈ I, 0 < (1 : ℝ) * (s - a)) ∨ (∀ s ∈ I, 0 < (-1 : ℝ) * (s - a)) := by
    by_cases hleft : ∃ s ∈ I, s < a
    · obtain ⟨s, hsI, hsa⟩ := hleft
      refine Or.inr fun t htI => ?_
      have hta : t < a := by
        rcases lt_trichotomy t a with h | h | h
        · exact h
        · exact absurd (h ▸ htI) haI
        · exact absurd (hord.out hsI htI ⟨le_of_lt hsa, le_of_lt h⟩) haI
      simp only [neg_mul, one_mul]
      linarith
    · refine Or.inl fun t htI => ?_
      have hat : a ≤ t := not_lt.1 fun h => hleft ⟨t, htI, h⟩
      simp only [one_mul]
      rcases lt_or_eq_of_le hat with h | h
      · linarith
      · exact absurd (h ▸ htI) haI
  -- the branch
  rcases hside with hs | hs
  · obtain ⟨hγ, ⟨b, hb, hbranch⟩, hnear⟩ :=
      IsProperLineParam.exists_branch hγ₀ hord hne hacl (Or.inl rfl) hs
    exact ⟨fun t => γ₀ (a + 1 * t), L, hγ, by simp, hrange ▸ image_subset_range γ₀ I,
      ⟨b, hb, hbranch⟩, hnear⟩
  · obtain ⟨hγ, ⟨b, hb, hbranch⟩, hnear⟩ :=
      IsProperLineParam.exists_branch hγ₀ hord hne hacl (Or.inr rfl) hs
    exact ⟨fun t => γ₀ (a + (-1) * t), L, hγ, by simp, hrange ▸ image_subset_range γ₀ I,
      ⟨b, hb, hbranch⟩, hnear⟩


/-- **At least three edges of the Voronoi diagram end at a Voronoi vertex.**

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
three do (`AVD.CurveSystem.three_le_faces_at_vertex`). -/
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

/-- The counting form of `AVD.CurveSystem.exists_two_edges_at_vertex`: at least two edges of
the Voronoi diagram have a given Voronoi vertex in their closure. -/
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

end CurveSystem

end AVD
