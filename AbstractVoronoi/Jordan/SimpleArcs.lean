import AbstractVoronoi.Jordan.ArcSurgery

/-!
# Simple arcs in open connected sets and in the complement of an arc

Two elementary facts of plane topology, proved without the Jordan curve theorem:

* `AVD.exists_isArc_of_isPreconnected`: two points of an open preconnected set `Ω` of the
  plane are joined by a simple arc inside `Ω`.  The points joined to `x` by an arc in `Ω`
  form a set which is open and closed in `Ω`: near a point `p` of a ball contained in `Ω`
  and joined to `x` by an arc `γ`, every other point `z` of the ball is joined to `x` by
  following the segment from `z` towards `p` until it first meets `γ`, then `γ` back to `x`.
* `AVD.exists_isArc_compl_arc`: two points off a simple arc `A` are joined by a simple arc
  avoiding `A`.  The complement of a simple arc is open and connected
  (`AVD.Backend.isConnected_compl_arc`), so the first result applies to it.

The first result is also stated as `AVD.exists_arc_in_open`, the name used in the rest of
the development.  Both results used to be taken from the planar-topology backend; they are
proved here from the arc surgery of `AbstractVoronoi.Jordan.ArcSurgery` and, for the
complement of an arc, from `AVD.Backend.isConnected_compl_arc`.
-/

open Set Topology Metric

namespace AVD

/-- The straight segment from `z` to `p`, parametrized affinely. -/
theorem isArc_segmentParam {z p : Plane} (hzp : z ≠ p) :
    IsArc (fun t : ℝ => z + t • (p - z)) := by
  refine ⟨by fun_prop, ?_⟩
  intro s _ t _ hst
  have h : s • (p - z) = t • (p - z) := add_left_cancel hst
  exact smul_left_injective ℝ (sub_ne_zero.2 hzp.symm) h

/-- The segment parametrization traverses the closed segment. -/
theorem segmentParam_image (z p : Plane) :
    (fun t : ℝ => z + t • (p - z)) '' Icc 0 1 = segment ℝ z p :=
  (segment_eq_image' ℝ z p).symm

/-- The points joined to `x` by an arc inside `Ω`, together with `x` itself. -/
private def joinedSet (Ω : Set Plane) (x : Plane) : Set Plane :=
  {z | z ∈ Ω ∧ (z = x ∨ ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = z ∧ γ '' Icc 0 1 ⊆ Ω)}

/-- **The local step.** If a ball contained in `Ω` contains a point joined to `x` inside `Ω`,
then every point of the ball is joined to `x` inside `Ω`. -/
private theorem mem_joinedSet_of_ball {Ω : Set Plane} {x c p z : Plane} {r : ℝ}
    (hB : ball c r ⊆ Ω) (hp : p ∈ ball c r) (hpJ : p ∈ joinedSet Ω x) (hz : z ∈ ball c r) :
    z ∈ joinedSet Ω x := by
  refine ⟨hB hz, ?_⟩
  by_cases hzx : z = x
  · exact Or.inl hzx
  right
  by_cases hzp : z = p
  · subst hzp
    rcases hpJ.2 with h | h
    · exact absurd h hzx
    · exact h
  -- the segment from `z` to `p` lies in the ball
  have hseg : segment ℝ z p ⊆ Ω :=
    ((convex_ball c r).segment_subset hz hp).trans hB
  rcases hpJ.2 with rfl | ⟨γ, hγ, hγ0, hγ1, hγΩ⟩
  · -- `p = x`: the segment from `x` to `z`
    refine ⟨fun t => p + t • (z - p), isArc_segmentParam (Ne.symm hzp), by simp, by simp, ?_⟩
    rw [segmentParam_image, segment_symm]
    exact hseg
  by_cases hzγ : z ∈ γ '' Icc 0 1
  · -- `z` lies on `γ`: take the initial piece of `γ`
    obtain ⟨t, ht, rfl⟩ := hzγ
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le ht.1 with h | h
      · exact absurd (by rw [← h, hγ0]) hzx
      · exact h
    refine ⟨subarcParam γ 0 t, hγ.subarc le_rfl ht0 ht.2, by rw [subarcParam_zero, hγ0],
      subarcParam_one _ _ _, ?_⟩
    rw [subarcParam_image ht0.le]
    exact (image_mono (Icc_subset_Icc le_rfl ht.2)).trans hγΩ
  · -- follow the segment from `z` until it meets `γ`, then `γ` back to `x`
    have hτimg : revParam γ '' Icc 0 1 = γ '' Icc 0 1 := revParam_image γ
    obtain ⟨δ, hδ, hδ0, hδ1, hδimg⟩ := exists_arc_cut (isArc_segmentParam hzp) hγ.rev
      (by simpa [hτimg] using hzγ)
      (by rw [hτimg]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [hγ1]⟩)
    refine ⟨revParam δ, hδ.rev, by rw [revParam_zero, hδ1, revParam_one, hγ0],
      by rw [revParam_one, hδ0]; simp, ?_⟩
    rw [revParam_image]
    refine hδimg.trans (union_subset ?_ ?_)
    · rw [segmentParam_image]; exact hseg
    · rw [hτimg]; exact hγΩ

/-- **Simple arcs in open connected sets.** Two distinct points of an open preconnected set
`Ω` of the plane are joined by a simple arc inside `Ω`. -/
theorem exists_isArc_of_isPreconnected {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {x y : Plane} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = y ∧ γ '' Icc 0 1 ⊆ Ω := by
  have hopen : IsOpen (joinedSet Ω x) := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hΩ z hz.1
    exact ⟨r, hr, fun w hw => mem_joinedSet_of_ball hB (mem_ball_self hr) hz hw⟩
  have hclosed : closure (joinedSet Ω x) ∩ Ω ⊆ joinedSet Ω x := by
    rintro z ⟨hzc, hzΩ⟩
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hΩ z hzΩ
    obtain ⟨p, hpJ, hpB⟩ := Metric.mem_closure_iff.1 hzc r hr
    exact mem_joinedSet_of_ball hB (by rw [mem_ball, dist_comm]; exact hpB) hpJ
      (mem_ball_self hr)
  have hsub : Ω ⊆ joinedSet Ω x :=
    hconn.subset_of_closure_inter_subset hopen ⟨x, hx, hx, Or.inl rfl⟩ hclosed
  rcases (hsub hy).2 with h | h
  · exact absurd h.symm hxy
  · exact h

/-- **The complement of a simple arc is connected** (`Backend.isConnected_compl_arc`). -/
theorem isConnected_compl_image_of_isArc {γ : ℝ → Plane} (hγ : IsArc γ) :
    IsConnected (γ '' Icc 0 1)ᶜ :=
  Backend.isConnected_compl_arc ⟨γ, hγ.cont, hγ.inj, rfl⟩

/-- **Simple arcs off a simple arc.** Two distinct points off a simple arc are joined by a
simple arc avoiding it. -/
theorem exists_isArc_compl_arc {γ : ℝ → Plane} (hγ : IsArc γ) {u w : Plane} (huw : u ≠ w)
    (hu : u ∉ γ '' Icc 0 1) (hw : w ∉ γ '' Icc 0 1) :
    ∃ δ : ℝ → Plane, IsArc δ ∧ δ 0 = u ∧ δ 1 = w ∧ δ '' Icc 0 1 ⊆ (γ '' Icc 0 1)ᶜ :=
  exists_isArc_of_isPreconnected
    (isCompact_Icc.image_of_continuousOn hγ.cont).isClosed.isOpen_compl
    (isConnected_compl_image_of_isArc hγ).isPreconnected hu hw huw

/-- Two distinct points of an open connected subset of the plane are joined by an arc
inside it.  This is the plane instance of the classical fact, quoted in footnote 5 of
Klein–Langetepe–Nilforoushan (2009), that a connected open set is arcwise connected; it is
`AVD.exists_isArc_of_isPreconnected` under the name used in the rest of the development. -/
theorem exists_arc_in_open {R : Set Plane} (hopen : IsOpen R) (hconn : IsPreconnected R)
    {x y : Plane} (hx : x ∈ R) (hy : y ∈ R) (hxy : x ≠ y) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x ∧ γ 1 = y ∧ γ '' Icc 0 1 ⊆ R :=
  exists_isArc_of_isPreconnected hopen hconn hx hy hxy

end AVD
