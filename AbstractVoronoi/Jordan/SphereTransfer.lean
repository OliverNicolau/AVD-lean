import AbstractVoronoi.Jordan.Schoenflies

/-!
# Transferring the Jordan curve theorem to the unbounded curves of axiom `A₁`

Axiom `A₁` of Definition 1 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

says that a bisecting curve `J(p,q)` becomes a closed Jordan curve *through the north pole*
after stereographic projection to the sphere (`AVD.IsUnboundedJordanCurve`).  **Theorem 4**
of the paper is applied to such curves as well, "applied to `J(p,r)` on the sphere" in the
words of the proof of Lemma 8.

This file carries out that transfer for the global part of Theorem 4: an unbounded Jordan
curve `C` splits the plane into two domains `D₁, D₂` whose common boundary is `C`.  The
route is the one indicated by the paper: the stereographic completion `K` of `C` is a closed
Jordan curve of the sphere; choosing a point `v` of the sphere off `K` and projecting
stereographically *from `v`* turns `K` into a closed Jordan curve of the plane, to which
`AVD.IsClosedJordanCurve.exists_separation_frontier_eq` applies; pulling the two
complementary domains back to the sphere, and adding the puncture `v` to the one coming from
the unbounded domain, splits the sphere; projecting from the north pole finally returns to
the plane.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-! ## A plane curve with a proper line parametrization is not the whole plane -/

/-- A properly embedded line does not fill the plane.  (Otherwise its parametrization would
be a homeomorphism `ℝ ≃ ℝ²`, and removing one point would disconnect the plane.)  This is
what guarantees that there is a point of the sphere off the stereographic completion of a
bisecting curve, so that the sphere can be charted away from that curve. -/
theorem exists_notMem_of_properLineParam {γ : ℝ → Plane} {C : Set Plane}
    (h : IsProperLineParam γ C) : ∃ x : Plane, x ∉ C := by
  obtain ⟨hcont, hinj, hrange, hproper⟩ := h
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective γ := by
    intro x
    have : x ∈ C := hcon x
    rw [← hrange] at this
    exact this
  have hproper' : IsProperMap γ :=
    isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => hproper K hK⟩
  have hclosed : IsClosedMap γ := hproper'.isClosedMap
  -- a continuous closed bijection is an open map
  have hopen : IsOpenMap γ := by
    intro U hU
    have himg : γ '' U = (γ '' Uᶜ)ᶜ := by
      apply Subset.antisymm
      · rintro x ⟨u, hu, rfl⟩ ⟨u', hu', hu'x⟩
        exact hu' (hinj hu'x ▸ hu)
      · intro x hx
        obtain ⟨u, rfl⟩ := hsurj x
        by_cases hu : u ∈ U
        · exact ⟨u, hu, rfl⟩
        · exact absurd ⟨u, hu, rfl⟩ hx
    rw [himg]
    exact (hclosed _ hU.isClosed_compl).isOpen_compl
  -- but then the plane minus a point would be disconnected
  have hconn : IsConnected ({γ 0}ᶜ : Set Plane) :=
    isConnected_compl_singleton_of_one_lt_rank one_lt_rank_plane _
  have hcover : ({γ 0}ᶜ : Set Plane) ⊆ γ '' Iio 0 ∪ γ '' Ioi 0 := by
    intro x hx
    obtain ⟨u, rfl⟩ := hsurj x
    rcases lt_trichotomy u 0 with h | h | h
    · exact Or.inl ⟨u, h, rfl⟩
    · exact absurd (by rw [h] : γ u = γ 0) hx
    · exact Or.inr ⟨u, h, rfl⟩
  have hdisj : Disjoint (γ '' Iio 0) (γ '' Ioi 0) := by
    rw [Set.disjoint_left]
    rintro x ⟨u, hu, rfl⟩ ⟨u', hu', hu'x⟩
    have heq : u' = u := hinj hu'x
    have h1 : (0 : ℝ) < u := heq ▸ hu'
    have h2 : u < 0 := hu
    linarith
  have hm1 : γ (-1) ∈ ({γ 0}ᶜ : Set Plane) := fun h => by
    have := hinj h; linarith
  have hp1 : γ 1 ∈ ({γ 0}ᶜ : Set Plane) := fun h => by
    have := hinj h; linarith
  rcases hconn.isPreconnected.subset_or_subset (hopen _ isOpen_Iio) (hopen _ isOpen_Ioi)
    hdisj hcover with hsub | hsub
  · exact (Set.disjoint_left.1 hdisj) (hsub hp1) ⟨1, by norm_num, rfl⟩
  · exact (Set.disjoint_left.1 hdisj) ⟨-1, by norm_num, rfl⟩ (hsub hm1)

/-! ## Separation of the sphere by a closed Jordan curve -/

/-- **A closed Jordan curve of the sphere separates the sphere**, provided there is a point
of the sphere off the curve: the complement consists of two disjoint open connected sets,
each of which has the whole curve in its closure.

The proof charts the sphere away from a point `v` off the curve; the curve becomes a closed
Jordan curve of the plane, for which the assertion is
`AVD.IsClosedJordanCurve.exists_separation_frontier_eq`.  The puncture `v` is then added
back to the domain coming from the *unbounded* complementary domain in the chart. -/
theorem sphere_separation {K : Set Sphere} (hK : IsClosedJordanCurve K) {v : Sphere}
    (hv : v ∉ K) :
    ∃ F₁ F₂ : Set Sphere, IsOpen F₁ ∧ IsOpen F₂ ∧ IsConnected F₁ ∧ IsConnected F₂ ∧
      Disjoint F₁ F₂ ∧ F₁ ∪ F₂ = Kᶜ ∧ K ⊆ closure F₁ ∧ K ⊆ closure F₂ := by
  classical
  set Φ : OpenPartialHomeomorph Sphere Plane := stereographic' 2 v with hΦdef
  have hsrc : Φ.source = ({v}ᶜ : Set Sphere) := by simp [hΦdef]
  have htgt : Φ.target = (univ : Set Plane) := by simp [hΦdef]
  have hKsrc : K ⊆ Φ.source := by
    rw [hsrc]
    intro x hx hxv
    rw [mem_singleton_iff] at hxv
    exact hv (hxv ▸ hx)
  have hsymmcont : Continuous (Φ.symm : Plane → Sphere) := by
    have h := Φ.symm.continuousOn_toFun
    rw [show Φ.symm.source = univ by rw [Φ.symm_source, htgt]] at h
    exact continuousOn_univ.1 h
  have hright : ∀ y : Plane, Φ (Φ.symm y) = y := fun y => Φ.right_inv (by rw [htgt]; trivial)
  have hleft : ∀ z ∈ Φ.source, Φ.symm (Φ z) = z := fun z hz => Φ.left_inv hz
  have hsymminj : Function.Injective (Φ.symm : Plane → Sphere) :=
    Function.LeftInverse.injective hright
  have hsymmmem : ∀ y : Plane, Φ.symm y ∈ Φ.source := fun y => Φ.map_target (by rw [htgt]; trivial)
  -- the curve, seen in the chart
  set C' : Set Plane := Φ '' K with hC'def
  have hsymmC' : Φ.symm '' C' = K := by
    rw [hC'def, ← Set.image_comp]
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      simpa [Function.comp, hleft z (hKsrc hz)] using hz
    · intro z hz
      exact ⟨z, hz, by simpa [Function.comp] using hleft z (hKsrc hz)⟩
  have hC' : IsClosedJordanCurve C' := by
    obtain ⟨σ, hcont, hinj, hcl, himg⟩ := hK
    refine ⟨fun t => Φ (σ t), ?_, ?_, by change Φ (σ 0) = Φ (σ 1); rw [hcl], ?_⟩
    · refine Φ.continuousOn.comp hcont ?_
      intro t ht
      exact hKsrc (himg ▸ ⟨t, ht, rfl⟩)
    · intro s hs t ht hst
      have hst' : Φ (σ s) = Φ (σ t) := hst
      refine hinj hs ht ?_
      have hs' : σ s ∈ Φ.source := hKsrc (himg ▸ ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩)
      have ht' : σ t ∈ Φ.source := hKsrc (himg ▸ ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
      rw [← hleft _ hs', ← hleft _ ht', hst']
    · rw [hC'def, ← himg, Set.image_image]
  obtain ⟨E₁, E₂, h1o, h2o, h1c, h2c, hdisjE, hunionE, hf1, hf2, hbdd⟩ :=
    hC'.exists_separation_frontier_eq
  -- the main construction, for a bounded and an unbounded complementary domain in the chart
  have main : ∀ Eb Eu : Set Plane, IsOpen Eb → IsOpen Eu → IsConnected Eb → IsConnected Eu →
      Disjoint Eb Eu → Eb ∪ Eu = C'ᶜ → frontier Eb = C' → frontier Eu = C' →
      Bornology.IsBounded Eb → ¬ Bornology.IsBounded Eu →
      ∃ F₁ F₂ : Set Sphere, IsOpen F₁ ∧ IsOpen F₂ ∧ IsConnected F₁ ∧ IsConnected F₂ ∧
        Disjoint F₁ F₂ ∧ F₁ ∪ F₂ = Kᶜ ∧ K ⊆ closure F₁ ∧ K ⊆ closure F₂ := by
    intro Eb Eu hbo huo hbc huc hdisj hunion hfb hfu hbb hub
    set F₁ : Set Sphere := Φ.symm '' Eb with hF1def
    set G : Set Sphere := Φ.symm '' Eu with hGdef
    set F₂ : Set Sphere := G ∪ {v} with hF2def
    have hF1sub : F₁ ⊆ Φ.source := by rintro x ⟨y, -, rfl⟩; exact hsymmmem y
    have hGsub : G ⊆ Φ.source := by rintro x ⟨y, -, rfl⟩; exact hsymmmem y
    have hF1open : IsOpen F₁ :=
      Φ.isOpen_image_symm_of_subset_target hbo (by rw [htgt]; exact subset_univ _)
    have hGopen : IsOpen G :=
      Φ.isOpen_image_symm_of_subset_target huo (by rw [htgt]; exact subset_univ _)
    -- the sphere is partitioned into `F₁`, `G`, `K` and `{v}`
    have hcover : ∀ s : Sphere, s ∈ F₁ ∪ G ∪ K ∪ {v} := by
      intro s
      by_cases hsv : s = v
      · exact Or.inr hsv
      · have hssrc : s ∈ Φ.source := by rw [hsrc]; exact hsv
        by_cases hsK : Φ s ∈ C'
        · refine Or.inl (Or.inr ?_)
          rw [← hsymmC']
          exact ⟨Φ s, hsK, hleft s hssrc⟩
        · have : Φ s ∈ Eb ∪ Eu := by rw [hunion]; exact hsK
          rcases this with h | h
          · exact Or.inl (Or.inl (Or.inl ⟨Φ s, h, hleft s hssrc⟩))
          · exact Or.inl (Or.inl (Or.inr ⟨Φ s, h, hleft s hssrc⟩))
    have hvF1 : v ∉ F₁ := by
      rintro ⟨y, hy0, hy⟩
      have hmem := hsymmmem y
      rw [hy, hsrc] at hmem
      exact hmem rfl
    have hvG : v ∉ G := by
      rintro ⟨y, hy0, hy⟩
      have hmem := hsymmmem y
      rw [hy, hsrc] at hmem
      exact hmem rfl
    have hF1K : Disjoint F₁ K := by
      rw [Set.disjoint_left]
      rintro x ⟨y, hy, rfl⟩ hxK
      rw [← hsymmC'] at hxK
      obtain ⟨y', hy', hy'eq⟩ := hxK
      have heq : y' = y := hsymminj hy'eq
      have hyC' : y ∈ C'ᶜ := by rw [← hunion]; exact Or.inl hy
      exact hyC' (heq ▸ hy')
    have hGK : Disjoint G K := by
      rw [Set.disjoint_left]
      rintro x ⟨y, hy, rfl⟩ hxK
      rw [← hsymmC'] at hxK
      obtain ⟨y', hy', hy'eq⟩ := hxK
      have heq : y' = y := hsymminj hy'eq
      have hyC' : y ∈ C'ᶜ := by rw [← hunion]; exact Or.inr hy
      exact hyC' (heq ▸ hy')
    have hF1G : Disjoint F₁ G := by
      rw [Set.disjoint_left]
      rintro x ⟨y, hy, rfl⟩ ⟨y', hy', hy'eq⟩
      have : y' = y := hsymminj hy'eq
      subst this
      exact (Set.disjoint_left.1 hdisj) hy hy'
    -- `K ∪ F₁` is compact, hence closed, so `F₂` is open
    have hclosureEb : closure Eb = Eb ∪ C' := by
      have h1 : closure Eb = interior Eb ∪ frontier Eb := closure_eq_interior_union_frontier Eb
      rwa [hbo.interior_eq, hfb] at h1
    have hcompact : IsCompact (Φ.symm '' closure Eb) := by
      refine IsCompact.image ?_ hsymmcont
      exact Metric.isCompact_of_isClosed_isBounded isClosed_closure hbb.closure
    have hKF1 : K ∪ F₁ = Φ.symm '' closure Eb := by
      rw [hclosureEb, Set.image_union, hsymmC', hF1def, Set.union_comm]
    have hF2open : IsOpen F₂ := by
      have hcl : IsClosed (K ∪ F₁) := by rw [hKF1]; exact hcompact.isClosed
      have heq : F₂ = (K ∪ F₁)ᶜ := by
        apply Subset.antisymm
        · rintro x (hx | hx)
          · exact fun h => by
              rcases h with h | h
              · exact (Set.disjoint_left.1 hGK) hx h
              · exact (Set.disjoint_left.1 hF1G) h hx
          · rw [mem_singleton_iff] at hx
            subst hx
            exact fun h => by rcases h with h | h; exacts [hv h, hvF1 h]
        · intro x hx
          rcases hcover x with ((h | h) | h) | h
          · exact absurd (Or.inr h) hx
          · exact Or.inl h
          · exact absurd (Or.inl h) hx
          · exact Or.inr h
      rw [heq]
      exact hcl.isOpen_compl
    -- the puncture lies in the closure of the unbounded domain
    have hvclosure : v ∈ closure G := by
      by_contra hcon
      have hsub : closure G ⊆ Φ.source := by
        rw [hsrc]
        intro x hx hxv
        rw [mem_singleton_iff] at hxv
        exact hcon (hxv ▸ hx)
      have hcompG : IsCompact (closure G) := isClosed_closure.isCompact
      have hEu : Eu ⊆ Φ '' closure G := by
        intro y hy
        exact ⟨Φ.symm y, subset_closure ⟨y, hy, rfl⟩, hright y⟩
      exact hub (((hcompG.image_of_continuousOn (Φ.continuousOn.mono hsub)).isBounded).subset hEu)
    -- the curve lies in the closure of both domains
    have hKclF1 : K ⊆ closure F₁ := by
      rw [← hsymmC']
      refine (Set.image_mono ?_).trans (image_closure_subset_closure_image hsymmcont)
      rw [hclosureEb]; exact subset_union_right
    have hKclG : K ⊆ closure G := by
      rw [← hsymmC']
      have h2 : closure Eu = Eu ∪ C' := by
        have h1 : closure Eu = interior Eu ∪ frontier Eu := closure_eq_interior_union_frontier Eu
        rwa [huo.interior_eq, hfu] at h1
      refine (Set.image_mono ?_).trans (image_closure_subset_closure_image hsymmcont)
      rw [h2]; exact subset_union_right
    refine ⟨F₁, F₂, hF1open, hF2open, hbc.image _ (hsymmcont.continuousOn), ?_, ?_, ?_,
      hKclF1, (hKclG.trans (closure_mono subset_union_left))⟩
    · -- `F₂` is connected: it lies between `G` and its closure
      refine IsConnected.subset_closure (huc.image _ (hsymmcont.continuousOn)) subset_union_left ?_
      rintro x (hx | hx)
      · exact subset_closure hx
      · rw [mem_singleton_iff] at hx; exact hx ▸ hvclosure
    · rw [hF2def]
      rw [Set.disjoint_union_right]
      exact ⟨hF1G, by
        rw [Set.disjoint_singleton_right]; exact hvF1⟩
    · apply Subset.antisymm
      · rintro x (hx | (hx | hx))
        · exact fun h => (Set.disjoint_left.1 hF1K) hx h
        · exact fun h => (Set.disjoint_left.1 hGK) hx h
        · rw [mem_singleton_iff] at hx; exact hx ▸ hv
      · intro x hx
        rcases hcover x with ((h | h) | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact absurd h hx
        · exact Or.inr (Or.inr h)
  rcases hbdd with ⟨hb1, hu2⟩ | ⟨hb2, hu1⟩
  · exact main E₁ E₂ h1o h2o h1c h2c hdisjE hunionE hf1 hf2 hb1 hu2
  · obtain ⟨F₁, F₂, a, b, c, d, e, f, g, h⟩ :=
      main E₂ E₁ h2o h1o h2c h1c hdisjE.symm (by rw [union_comm]; exact hunionE) hf2 hf1 hb2 hu1
    exact ⟨F₂, F₁, b, a, d, c, e.symm, by rw [union_comm]; exact f, h, g⟩

/-! ## The global part of Theorem 4 for the unbounded curves of axiom `A₁` -/

/-- **The global assertions of Theorem 4** of Klein–Langetepe–Nilforoushan (2009) for the
*unbounded* Jordan curves of axiom `A₁`:

> Let `C` be a plane curve, homeomorphic to a line bisecting the plane.  Then `ℝ² \ C`
> consists of two domains `D₁, D₂` with common boundary `C`.

The proof transfers `AVD.IsClosedJordanCurve.exists_separation_frontier_eq` through the
sphere, exactly as the paper does ("by Theorem 4, applied to `J(p,r)` on the sphere"). -/
theorem IsUnboundedJordanCurve.exists_separation_frontier_eq {C : Set Plane}
    (h : IsUnboundedJordanCurve C) :
    ∃ D₁ D₂ : Set Plane, IsOpen D₁ ∧ IsOpen D₂ ∧ IsConnected D₁ ∧ IsConnected D₂ ∧
      Disjoint D₁ D₂ ∧ D₁ ∪ D₂ = Cᶜ ∧ frontier D₁ = C ∧ frontier D₂ = C := by
  classical
  set K : Set Sphere := sphereCompletion C with hKdef
  -- a point of the sphere off the curve
  obtain ⟨γ, hγ⟩ := h.exists_properParam
  obtain ⟨x, hx⟩ := exists_notMem_of_properLineParam hγ
  have hvK : stereo.symm x ∉ K := by
    rintro (⟨y, hy, hyx⟩ | hcon)
    · exact hx (stereo_symm_injective hyx ▸ hy)
    · exact stereo_symm_ne_northPole x hcon
  obtain ⟨F₁, F₂, h1o, h2o, h1c, h2c, hdisj, hunion, hcl1, hcl2⟩ := sphere_separation h hvK
  -- the north pole lies on the curve, so the two domains avoid it
  have hN : northPole ∈ K := Or.inr rfl
  have hFsrc : ∀ F : Set Sphere, F ⊆ Kᶜ → F ⊆ stereo.source := by
    intro F hF z hz
    rw [stereo_source]
    intro hzN
    rw [mem_singleton_iff] at hzN
    exact hF hz (hzN ▸ hN)
  have hF1src : F₁ ⊆ stereo.source := hFsrc F₁ (hunion ▸ subset_union_left)
  have hF2src : F₂ ⊆ stereo.source := hFsrc F₂ (hunion ▸ subset_union_right)
  set D₁ : Set Plane := stereo '' F₁ with hD1def
  set D₂ : Set Plane := stereo '' F₂ with hD2def
  have hstereoinj : InjOn (stereo : Sphere → Plane) stereo.source := stereo.injOn
  have hD1open : IsOpen D₁ := stereo.isOpen_image_of_subset_source h1o hF1src
  have hD2open : IsOpen D₂ := stereo.isOpen_image_of_subset_source h2o hF2src
  have hD1conn : IsConnected D₁ := h1c.image _ (stereo.continuousOn.mono hF1src)
  have hD2conn : IsConnected D₂ := h2c.image _ (stereo.continuousOn.mono hF2src)
  have hDdisj : Disjoint D₁ D₂ := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hbz⟩
    have : b = a := hstereoinj (hF2src hb) (hF1src ha) hbz
    subst this
    exact (Set.disjoint_left.1 hdisj) ha hb
  -- the two domains cover the complement of the curve
  have hCimg : ∀ y : Plane, y ∈ C ↔ stereo.symm y ∈ K := by
    intro y
    constructor
    · intro hy; exact Or.inl ⟨y, hy, rfl⟩
    · rintro (⟨z, hz, hzy⟩ | hcon)
      · exact stereo_symm_injective hzy ▸ hz
      · exact absurd hcon (stereo_symm_ne_northPole y)
  have hDunion : D₁ ∪ D₂ = Cᶜ := by
    apply Subset.antisymm
    · rintro z (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · intro hz
        rw [hCimg, stereo_symm_stereo (by
          have hm := hF1src ha; rw [stereo_source] at hm; simpa using hm)] at hz
        have hmem : a ∈ F₁ ∪ F₂ := Or.inl ha
        rw [hunion] at hmem
        exact hmem hz
      · intro hz
        rw [hCimg, stereo_symm_stereo (by
          have hm := hF2src ha; rw [stereo_source] at hm; simpa using hm)] at hz
        have hmem : a ∈ F₁ ∪ F₂ := Or.inr ha
        rw [hunion] at hmem
        exact hmem hz
    · intro z hz
      have hzK : stereo.symm z ∉ K := fun hc => hz ((hCimg z).2 hc)
      have : stereo.symm z ∈ F₁ ∪ F₂ := by rw [hunion]; exact hzK
      rcases this with hc | hc
      · exact Or.inl ⟨stereo.symm z, hc, stereo_stereo_symm z⟩
      · exact Or.inr ⟨stereo.symm z, hc, stereo_stereo_symm z⟩
  -- the curve lies in the closure of both domains
  have hCcl : ∀ F : Set Sphere, F ⊆ stereo.source → K ⊆ closure F → C ⊆ closure (stereo '' F) := by
    intro F hFsrc' hKF y hy
    rw [_root_.mem_closure_iff]
    intro V hVopen hyV
    have hsy : stereo.symm y ∈ K := (hCimg y).1 hy
    have hsyF : stereo.symm y ∈ closure F := hKF hsy
    have hWopen : IsOpen (stereo.source ∩ stereo ⁻¹' V) :=
      stereo.continuousOn.isOpen_inter_preimage stereo.open_source hVopen
    have hsyW : stereo.symm y ∈ stereo.source ∩ stereo ⁻¹' V := by
      refine ⟨stereo_symm_apply_mem_source y, ?_⟩
      simp only [mem_preimage, stereo_stereo_symm]
      exact hyV
    obtain ⟨f, hfW, hfF⟩ := _root_.mem_closure_iff.1 hsyF _ hWopen hsyW
    exact ⟨stereo f, hfW.2, ⟨f, hfF, rfl⟩⟩
  have hfront : ∀ D E : Set Plane, IsOpen D → IsOpen E → Disjoint D E → D ∪ E = Cᶜ →
      C ⊆ closure D → frontier D = C := by
    intro D E hDo hEo hdis hun hCD
    have hDC : Disjoint D C := by
      rw [Set.disjoint_left]
      intro z hzD hzC
      exact (by rw [← hun]; exact Or.inl hzD : z ∈ Cᶜ) hzC
    have hdc : Disjoint (closure D) E := hdis.closure_left hEo
    have hsub : closure D ⊆ D ∪ C := by
      intro z hz
      by_cases hzD : z ∈ D
      · exact Or.inl hzD
      · by_cases hzC : z ∈ C
        · exact Or.inr hzC
        · have hmem : z ∈ D ∪ E := by rw [hun]; exact hzC
          rcases hmem with h | h
          · exact absurd h hzD
          · exact absurd h (Set.disjoint_left.1 hdc hz)
    rw [hDo.frontier_eq]
    apply Subset.antisymm
    · rintro z ⟨hz1, hz2⟩
      rcases hsub hz1 with h | h
      · exact absurd h hz2
      · exact h
    · intro z hz
      exact ⟨hCD hz, fun hc => (Set.disjoint_left.1 hDC) hc hz⟩
  exact ⟨D₁, D₂, hD1open, hD2open, hD1conn, hD2conn, hDdisj, hDunion,
    hfront D₁ D₂ hD1open hD2open hDdisj hDunion (hCcl F₁ hF1src hcl1),
    hfront D₂ D₁ hD2open hD1open hDdisj.symm (by rw [union_comm]; exact hDunion)
      (hCcl F₂ hF2src hcl2)⟩

end AVD
