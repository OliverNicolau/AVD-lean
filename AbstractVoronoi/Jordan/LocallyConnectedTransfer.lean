import AbstractVoronoi.Jordan.LocalConnectivity

/-!
# Local connectedness is a topological, local notion

The local connectedness `AVD.LocallyConnectedAt D z` of a plane set at a point is stated in
`AbstractVoronoi.Jordan.LocalConnectivity` in metric terms (for every `ε > 0` there is a
`δ > 0` such that two points of `D` within `δ` of `z` are joined inside `D ∩ ball z ε`).
This file records that it is nevertheless

* a *topological* notion (`AVD.locallyConnectedAt_iff_nhds`), so that it transports along a
  homeomorphism of the plane (`AVD.LocallyConnectedAt.of_image_homeomorph`), and
* a *local* notion (`AVD.locallyConnectedAt_of_inter_ball_eq`), so that it only depends on
  the trace of `D` on an arbitrarily small ball around `z`.

Both are used to transfer the Jordan–Schönflies theorem of the dependency to the local
structure of the curves of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

which is the local part of **Theorem 4** of that paper.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- Two points of a set that contains the segment joining them are joined inside it. -/
theorem joinedIn_of_segment_subset {T : Set Plane} {a b : Plane}
    (h : segment ℝ a b ⊆ T) : JoinedIn T a b := by
  have hpc : IsPathConnected (segment ℝ a b) :=
    (convex_segment a b).isPathConnected ⟨a, left_mem_segment ℝ a b⟩
  exact (hpc.joinedIn a (left_mem_segment ℝ a b) b (right_mem_segment ℝ a b)).mono h

/-- **Local connectedness is a topological notion**: `AVD.LocallyConnectedAt D z` says
exactly that every neighbourhood `V` of `z` contains the traces of `D` on a smaller
neighbourhood `W` of `z` in a single "joinable" piece. -/
theorem locallyConnectedAt_iff_nhds {D : Set Plane} {z : Plane} :
    LocallyConnectedAt D z ↔
      ∀ V ∈ 𝓝 z, ∃ W ∈ 𝓝 z, ∀ x ∈ D ∩ W, ∀ y ∈ D ∩ W, JoinedIn (D ∩ V) x y := by
  constructor
  · intro h V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨δ, hδ, hjoin⟩ := h ε hε
    refine ⟨ball z δ, ball_mem_nhds z hδ, fun x hx y hy => ?_⟩
    exact (hjoin x hx y hy).mono (inter_subset_inter_right D hεV)
  · intro h ε hε
    obtain ⟨W, hW, hjoin⟩ := h (ball z ε) (ball_mem_nhds z hε)
    obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.1 hW
    exact ⟨δ, hδ, fun x hx y hy => hjoin x ⟨hx.1, hδW hx.2⟩ y ⟨hy.1, hδW hy.2⟩⟩

/-- **Local connectedness transports along a homeomorphism of the plane.** -/
theorem LocallyConnectedAt.of_image_homeomorph {D : Set Plane} {z : Plane} (F : Plane ≃ₜ Plane)
    (h : LocallyConnectedAt (F '' D) (F z)) : LocallyConnectedAt D z := by
  rw [locallyConnectedAt_iff_nhds] at h ⊢
  intro V hV
  have hV' : F '' V ∈ 𝓝 (F z) := by
    rw [← F.map_nhds_eq z]
    exact Filter.image_mem_map hV
  obtain ⟨W', hW', hjoin⟩ := h (F '' V) hV'
  refine ⟨F ⁻¹' W', F.continuous.continuousAt.preimage_mem_nhds (by simpa using hW'), ?_⟩
  intro x hx y hy
  have hFx : F x ∈ F '' D ∩ W' := ⟨⟨x, hx.1, rfl⟩, hx.2⟩
  have hFy : F y ∈ F '' D ∩ W' := ⟨⟨y, hy.1, rfl⟩, hy.2⟩
  have hjoined := (hjoin _ hFx _ hFy).map F.symm.continuous
  have himg : F.symm '' (F '' D ∩ F '' V) = D ∩ V := by
    rw [← Set.image_inter F.injective, ← Set.image_comp]
    simp
  rw [himg] at hjoined
  simpa using hjoined

/-- **Local connectedness transports along a homeomorphism defined near the point.**  If `e`
is a homeomorphism between two open subsets of the plane, `z` lies in its source and the
image of `D` is locally connected at `e z`, then `D` is locally connected at `z`.

This is the form needed for the unbounded curves of axiom `A₁` of
Klein–Langetepe–Nilforoushan (2009), which become closed Jordan curves only after a chart
of the sphere that is undefined at one point of the plane. -/
theorem LocallyConnectedAt.of_openPartialHomeomorph {D : Set Plane} {z : Plane}
    (e : OpenPartialHomeomorph Plane Plane) (hz : z ∈ e.source)
    (h : LocallyConnectedAt (e '' (D ∩ e.source)) (e z)) : LocallyConnectedAt D z := by
  set A : Set Plane := e '' (D ∩ e.source) with hA
  rw [locallyConnectedAt_iff_nhds] at h ⊢
  intro V hV
  -- an open neighbourhood of `z` inside `V` and inside the source
  obtain ⟨O, hOV, hOopen, hzO⟩ := _root_.mem_nhds_iff.1 hV
  set V₀ : Set Plane := O ∩ e.source with hV₀
  have hV₀open : IsOpen V₀ := hOopen.inter e.open_source
  have hzV₀ : z ∈ V₀ := ⟨hzO, hz⟩
  have hV₀src : V₀ ⊆ e.source := inter_subset_right
  set V' : Set Plane := e '' V₀ with hV'
  have hV'open : IsOpen V' := e.isOpen_image_of_subset_source hV₀open hV₀src
  have hV'mem : V' ∈ 𝓝 (e z) := hV'open.mem_nhds ⟨z, hzV₀, rfl⟩
  obtain ⟨W', hW', hjoin⟩ := h V' hV'mem
  refine ⟨e ⁻¹' W' ∩ e.source, Filter.inter_mem ((e.continuousAt hz) hW')
    (e.open_source.mem_nhds hz), ?_⟩
  intro x hx y hy
  have hxA : e x ∈ A ∩ W' := ⟨⟨x, ⟨hx.1, hx.2.2⟩, rfl⟩, hx.2.1⟩
  have hyA : e y ∈ A ∩ W' := ⟨⟨y, ⟨hy.1, hy.2.2⟩, rfl⟩, hy.2.1⟩
  -- the image sets lie in the target, where the inverse is continuous
  have hAtgt : A ⊆ e.target := by
    rintro _ ⟨a, ha, rfl⟩
    exact e.map_source ha.2
  have hV'tgt : V' ⊆ e.target := by
    rintro _ ⟨a, ha, rfl⟩
    exact e.map_source (hV₀src ha)
  have hjoined := (hjoin _ hxA _ hyA).map_continuousOn
    (e.continuousOn_symm.mono (fun u hu => hAtgt hu.1))
  rw [e.left_inv hx.2.2, e.left_inv hy.2.2] at hjoined
  refine hjoined.mono ?_
  -- the inverse image of `A ∩ V'` is contained in `D ∩ V`
  rintro _ ⟨u, ⟨⟨a, ha, rfl⟩, hu'⟩, rfl⟩
  obtain ⟨b, hb, hbu⟩ := hu'
  have hab : a = b := e.injOn ha.2 (hV₀src hb) hbu.symm
  rw [e.left_inv ha.2]
  exact ⟨ha.1, hOV (hab ▸ hb).1⟩

/-- **Local connectedness is a local notion**: it only depends on the trace of the set on a
ball around the point. -/
theorem locallyConnectedAt_of_inter_ball_eq {D D' : Set Plane} {z : Plane} {r : ℝ} (hr : 0 < r)
    (heq : D ∩ ball z r = D' ∩ ball z r) (h : LocallyConnectedAt D' z) :
    LocallyConnectedAt D z := by
  intro ε hε
  have hmin : 0 < min ε r := lt_min hε hr
  obtain ⟨δ, hδ, hjoin⟩ := h (min ε r) hmin
  refine ⟨min δ r, lt_min hδ hr, fun x hx y hy => ?_⟩
  -- the small ball around `z` sees the same points of `D` and of `D'`
  have hsub : ∀ w, w ∈ D ∩ ball z (min δ r) → w ∈ D' ∩ ball z δ := by
    intro w hw
    have hwr : w ∈ D ∩ ball z r :=
      ⟨hw.1, ball_subset_ball (min_le_right δ r) hw.2⟩
    rw [heq] at hwr
    exact ⟨hwr.1, ball_subset_ball (min_le_left δ r) hw.2⟩
  have hjoined := hjoin x (hsub x hx) y (hsub y hy)
  refine hjoined.mono ?_
  intro w hw
  have hwr : w ∈ D' ∩ ball z r :=
    ⟨hw.1, ball_subset_ball (min_le_right ε r) hw.2⟩
  rw [← heq] at hwr
  exact ⟨hwr.1, ball_subset_ball (min_le_left ε r) hw.2⟩

end AVD
