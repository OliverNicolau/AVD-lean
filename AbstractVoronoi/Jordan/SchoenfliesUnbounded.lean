import AbstractVoronoi.Jordan.SchoenfliesClosed
import AbstractVoronoi.Jordan.SphereTransfer

/-!
# The local structure of an unbounded Jordan curve, from the Jordan–Schönflies theorem

Axiom `A₁` of Definition 1 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

allows the bisecting curves to be *unbounded*: what is required is that the stereographic
completion of the curve be a closed Jordan curve of the sphere
(`AVD.IsUnboundedJordanCurve`).  **Theorem 4** is applied to those curves as well, "applied
to `J(p,r)` on the sphere" in the words of the proof of Lemma 8.

This file carries out, for such a curve, the transfer of the local part of Theorem 4 that
`AbstractVoronoi.Jordan.SchoenfliesClosed` proves for closed Jordan curves:
`AVD.IsUnboundedJordanCurve.locallyConnectedAt`.  The route is the one already used for the
global part in `AbstractVoronoi.Jordan.SphereTransfer`: the completion `K` of `C` is a closed
Jordan curve of the sphere; a point `v` of the sphere off `K` is chosen, and the chart
`Φ = stereographic' 2 v` turns `K` into a closed Jordan curve `C'` of the plane.  The
composition `e = stereo.symm.trans Φ` is then a homeomorphism from the plane *minus at most
one point* onto an open subset of the plane, carrying the complementary domains of `C` onto
those of `C'`; since local connectedness is a local and topological notion
(`AbstractVoronoi.Jordan.LocallyConnectedTransfer`), the statement for `C` at a point `z`
follows from the statement for `C'` at `e z`.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- The image of a closed Jordan curve under a map that is continuous and injective on it is
again a closed Jordan curve. -/
theorem IsClosedJordanCurve.image {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} (hK : IsClosedJordanCurve K) {f : X → Y} (hf : ContinuousOn f K)
    (hinj : InjOn f K) : IsClosedJordanCurve (f '' K) := by
  obtain ⟨σ, hcont, hsinj, hcl, himg⟩ := hK
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ K := fun t ht => himg ▸ ⟨t, ht, rfl⟩
  refine ⟨fun t => f (σ t), hf.comp hcont hmem, ?_, by simp [hcl], ?_⟩
  · intro s hs t ht hst
    refine hsinj hs ht ?_
    exact hinj (hmem s ⟨hs.1, hs.2.le⟩) (hmem t ⟨ht.1, ht.2.le⟩) hst
  · rw [← himg, Set.image_image]

/-- A nonempty open subset of the plane is not contained in a single point: it meets the
complement of any singleton. -/
theorem exists_mem_ne {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) (p : Plane) :
    ∃ x ∈ U, x ≠ p := by
  obtain ⟨q, hq⟩ := hne
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU q hq
    refine ⟨q + (r / 2) • (EuclideanSpace.single 0 1 : Plane), hball ?_, ?_⟩
    · have hnorm : ‖(r / 2) • (EuclideanSpace.single 0 1 : Plane)‖ = r / 2 := by
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
      rw [mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, hnorm]
      linarith
    · intro hcon
      have : (r / 2) • (EuclideanSpace.single 0 1 : Plane) = 0 := by
        have := hcon
        rwa [add_eq_left] at this
      rw [smul_eq_zero] at this
      rcases this with h | h
      · simp only [div_eq_zero_iff] at h
        rcases h with h | h <;> linarith
      · have : ‖(EuclideanSpace.single 0 1 : Plane)‖ = 1 := by
          rw [PiLp.norm_single, norm_one]
        rw [h, norm_zero] at this
        norm_num at this
  · exact ⟨q, hq, hqp⟩

/-- **The complementary domains of an unbounded Jordan curve are locally connected at the
points of the curve.**

This is the Jordan–Schönflies content of Theorem 4 of Klein–Langetepe–Nilforoushan (2009) for
the unbounded curves of axiom `A₁`, obtained from the closed case
(`AVD.IsClosedJordanCurve.locallyConnectedAt`) by charting the sphere away from a point off
the stereographic completion of the curve. -/
theorem IsUnboundedJordanCurve.locallyConnectedAt {C D₁ D₂ : Set Plane}
    (hC : IsUnboundedJordanCurve C) (h1o : IsOpen D₁) (h2o : IsOpen D₂)
    (h1c : IsConnected D₁) (h2c : IsConnected D₂) (hdisj : Disjoint D₁ D₂)
    (hunion : D₁ ∪ D₂ = Cᶜ) {z : Plane} (hz : z ∈ C) :
    LocallyConnectedAt D₁ z := by
  classical
  -- the completion of `C` on the sphere, and a point of the sphere off it
  set K : Set Sphere := sphereCompletion C with hKdef
  have hK : IsClosedJordanCurve K := hC
  obtain ⟨γ, hγ⟩ := hC.exists_properParam
  obtain ⟨x₀, hx₀⟩ := exists_notMem_of_properLineParam hγ
  set v : Sphere := stereo.symm x₀ with hvdef
  have hvK : v ∉ K := by
    rintro (⟨y, hy, hyv⟩ | hv)
    · exact hx₀ ((stereo_symm_injective hyv) ▸ hy)
    · rw [mem_singleton_iff] at hv
      exact stereo_symm_ne_northPole x₀ hv
  -- the chart of the sphere away from `v`
  set Φ : OpenPartialHomeomorph Sphere Plane := stereographic' 2 v with hΦdef
  have hsrc : Φ.source = ({v}ᶜ : Set Sphere) := by simp [hΦdef]
  have htgt : Φ.target = (univ : Set Plane) := by simp [hΦdef]
  have hKsrc : K ⊆ Φ.source := by
    rw [hsrc]
    intro s hs hsv
    rw [mem_singleton_iff] at hsv
    exact hvK (hsv ▸ hs)
  -- the curve in the chart
  set C' : Set Plane := Φ '' K with hC'def
  have hC' : IsClosedJordanCurve C' :=
    hK.image (Φ.continuousOn.mono hKsrc) (Φ.injOn.mono hKsrc)
  -- the composed chart of the plane
  set e : OpenPartialHomeomorph Plane Plane := stereo.symm.trans Φ with hedef
  have hesource : e.source = {x : Plane | stereo.symm x ≠ v} := by
    rw [hedef, OpenPartialHomeomorph.trans_source]
    ext x
    simp [hsrc]
  have heapply : ∀ x : Plane, e x = Φ (stereo.symm x) := fun x => rfl
  -- points of the curve, and `z` in particular, lie in the source
  have hCsrc : ∀ x ∈ C, x ∈ e.source := by
    intro x hx
    rw [hesource]
    intro hcon
    exact hvK (hcon ▸ (Or.inl ⟨x, hx, rfl⟩ : stereo.symm x ∈ K))
  have hzsrc : z ∈ e.source := hCsrc z hz
  have hzC' : e z ∈ C' := ⟨stereo.symm z, Or.inl ⟨z, hz, rfl⟩, rfl⟩
  -- the images of the two complementary domains
  set A : Set Plane := e '' (D₁ ∩ e.source) with hAdef
  set B : Set Plane := e '' (D₂ ∩ e.source) with hBdef
  have hAopen : IsOpen A :=
    e.isOpen_image_of_subset_source (h1o.inter e.open_source) inter_subset_right
  have hBopen : IsOpen B :=
    e.isOpen_image_of_subset_source (h2o.inter e.open_source) inter_subset_right
  have hABdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    have : b = a := e.injOn hb.2 ha.2 hba
    exact (Set.disjoint_left.1 hdisj ha.1) (this ▸ hb.1)
  -- `A ∪ B` is the complement of the curve in the chart
  have hAB : A ∪ B = C'ᶜ := by
    apply Subset.antisymm
    · rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;>
      · rintro ⟨k, hk, hke⟩
        have hka : stereo.symm a = k := by
          have hasrc : stereo.symm a ∈ Φ.source := by
            rw [hsrc]
            intro hcon
            rw [mem_singleton_iff] at hcon
            exact (hesource ▸ ha.2) hcon
          exact (Φ.injOn (hKsrc hk) hasrc hke).symm
        have haC : a ∈ C := by
          rcases hka ▸ hk with ⟨y, hy, hya⟩ | hN
          · exact (stereo_symm_injective hya) ▸ hy
          · rw [mem_singleton_iff] at hN
            exact absurd hN (stereo_symm_ne_northPole a)
        have : a ∈ Cᶜ := by
          rw [← hunion]
          first
          | exact Or.inl ha.1
          | exact Or.inr ha.1
        exact this haC
    · intro y hy
      -- the point of the sphere above `y`
      have hytgt : y ∈ Φ.target := by rw [htgt]; trivial
      set s : Sphere := Φ.symm y with hsdef
      have hssrc : s ∈ Φ.source := Φ.map_target hytgt
      have hsK : s ∉ K := by
        intro hcon
        exact hy ⟨s, hcon, Φ.right_inv hytgt⟩
      have hsN : s ≠ northPole := by
        intro hcon
        exact hsK (hcon ▸ (Or.inr rfl : northPole ∈ K))
      set a : Plane := stereo s with hadef
      have hasymm : stereo.symm a = s := stereo_symm_stereo hsN
      have hasrc : a ∈ e.source := by
        rw [hesource]
        change stereo.symm a ≠ v
        rw [hasymm]
        intro hcon
        rw [hcon, hsrc] at hssrc
        exact hssrc rfl
      have haC : a ∉ C := by
        intro hcon
        exact hsK (hasymm ▸ (Or.inl ⟨a, hcon, rfl⟩ : stereo.symm a ∈ K))
      have hea : e a = y := by
        rw [heapply, hasymm, hsdef, Φ.right_inv hytgt]
      have hacompl : a ∈ D₁ ∪ D₂ := by rw [hunion]; exact haC
      rcases hacompl with h | h
      · exact Or.inl ⟨a, ⟨h, hasrc⟩, hea⟩
      · exact Or.inr ⟨a, ⟨h, hasrc⟩, hea⟩
  -- both images are nonempty: the source misses at most one point of the plane
  have hsrc_ne : ∀ U : Set Plane, IsOpen U → U.Nonempty → (U ∩ e.source).Nonempty := by
    intro U hU hne
    by_cases hvN : v = northPole
    · obtain ⟨q, hq⟩ := hne
      refine ⟨q, hq, ?_⟩
      rw [hesource]
      intro hcon
      exact stereo_symm_ne_northPole q (hvN ▸ hcon)
    · obtain ⟨x, hx, hxne⟩ := exists_mem_ne hU hne (stereo v)
      refine ⟨x, hx, ?_⟩
      rw [hesource]
      intro hcon
      exact hxne (stereo_symm_injective (by rw [hcon, stereo_symm_stereo hvN]))
  have hAne : A.Nonempty := (hsrc_ne D₁ h1o h1c.nonempty).image e
  have hBne : B.Nonempty := (hsrc_ne D₂ h2o h2c.nonempty).image e
  -- the two complementary domains of the curve in the chart
  obtain ⟨E₁, E₂, hE1o, hE2o, hE1c, hE2c, hEdisj, hEunion, -, -, -⟩ :=
    hC'.exists_separation_frontier_eq
  have hcover : A ∪ B = E₁ ∪ E₂ := by rw [hAB, hEunion]
  have h1or := hE1c.isPreconnected.subset_or_subset hAopen hBopen hABdisj
    (by rw [hcover]; exact subset_union_left)
  have h2or := hE2c.isPreconnected.subset_or_subset hAopen hBopen hABdisj
    (by rw [hcover]; exact subset_union_right)
  have hA_eq : A = E₁ ∨ A = E₂ := by
    rcases h1or with h1 | h1
    · rcases h2or with h2 | h2
      · -- both domains inside `A`, so `B` is empty
        exfalso
        obtain ⟨b, hb⟩ := hBne
        have hbE : b ∈ E₁ ∪ E₂ := by rw [← hcover]; exact Or.inr hb
        have hbA : b ∈ A := by rcases hbE with h | h; exacts [h1 h, h2 h]
        exact (Set.disjoint_left.1 hABdisj hbA) hb
      · refine Or.inl (Subset.antisymm ?_ h1)
        intro p hp
        have hpE : p ∈ E₁ ∪ E₂ := by rw [← hcover]; exact Or.inl hp
        rcases hpE with h | h
        · exact h
        · exact absurd (h2 h) (Set.disjoint_left.1 hABdisj hp)
    · rcases h2or with h2 | h2
      · refine Or.inr (Subset.antisymm ?_ h2)
        intro p hp
        have hpE : p ∈ E₁ ∪ E₂ := by rw [← hcover]; exact Or.inl hp
        rcases hpE with h | h
        · exact absurd (h1 h) (Set.disjoint_left.1 hABdisj hp)
        · exact h
      · -- both domains inside `B`, so `A` is empty
        exfalso
        obtain ⟨a, ha⟩ := hAne
        have haE : a ∈ E₁ ∪ E₂ := by rw [← hcover]; exact Or.inl ha
        have haB : a ∈ B := by rcases haE with h | h; exacts [h1 h, h2 h]
        exact (Set.disjoint_left.1 hABdisj ha) haB
  have hmain : LocallyConnectedAt A (e z) := by
    rcases hA_eq with h | h
    · rw [h]; exact hC'.locallyConnectedAt hE1c hE2c hEunion hzC'
    · rw [h]
      exact hC'.locallyConnectedAt hE2c hE1c (by rw [union_comm]; exact hEunion) hzC'
  exact LocallyConnectedAt.of_openPartialHomeomorph e hzsrc hmain

end AVD
