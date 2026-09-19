import AbstractVoronoi.Jordan.PlaneTools

/-!
# The θ-curve theorem

The classical θ-curve theorem says that a crosscut `κ` of a complementary domain `D` of a
closed Jordan curve splits `D ∖ κ` into exactly the two Jordan domains `Ω₁, Ω₂` bounded by
`κ` and by the two arcs of the curve (the constructive half of that statement is
`AVD.exists_crosscut_domains`).  Classically it is deduced from Janiszewski's theorem.

Here it is deduced, instead, from the *local connectedness* of `D` at the points of the
curve — the hypothesis under which the local part of Theorem 4 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

is established in `AbstractVoronoi.Jordan.LocalAccessibility`.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- **The θ-curve theorem**, in the form in which it is used here.

Let `D` be an open set with frontier `C`, let `K` be a closed set whose complement is
connected (in the application, the image of a crosscut of `D`), and let `Ω₁, Ω₂` be two open
subsets of `D` with `frontier Ωᵢ = K ∪ Gᵢ` and `G₁ ∪ G₂ = C` (in the application, the two
domains cut off by the crosscut, as produced by `AVD.exists_crosscut_domains`).  If `D` is
locally connected at every point of `C`, then `Ω₁` and `Ω₂` exhaust `D ∖ K`.

The set `Ω₁ ∪ Ω₂` is open and closed in `D ∖ K`, so it is a union of connected components of
it; a component `V` missing it has, unless `V` is all of `Kᶜ`, a frontier point `y` on `C`,
and the local connectedness of `D` at `y` joins a point of `V` close to `y` to a point of
`Ω₁ ∪ Ω₂` close to `y` inside `D ∖ K`, a contradiction. -/
theorem crosscut_exhausts {D C K G₁ G₂ Ω₁ Ω₂ : Set Plane}
    (hDo : IsOpen D) (hfrD : frontier D = C) (hKclosed : IsClosed K)
    (hKcompl : IsPreconnected Kᶜ) (hCK : ∃ y ∈ C, y ∉ K)
    (hlc : ∀ y ∈ C, LocallyConnectedAt D y)
    (hΩ₁o : IsOpen Ω₁) (hΩ₂o : IsOpen Ω₂) (hΩ₁D : Ω₁ ⊆ D) (hΩ₂D : Ω₂ ⊆ D)
    (hfΩ₁ : frontier Ω₁ = K ∪ G₁) (hfΩ₂ : frontier Ω₂ = K ∪ G₂) (hG : G₁ ∪ G₂ = C) :
    D \ K ⊆ Ω₁ ∪ Ω₂ := by
  -- the domain is disjoint from its frontier
  have hDC : Disjoint D C := by
    rw [← hfrD, hDo.frontier_eq]
    exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx
  -- an open set is contained in itself together with its frontier
  have hclosure : ∀ S : Set Plane, IsOpen S → closure S ⊆ S ∪ frontier S := by
    intro S hS w hw
    by_cases h : w ∈ S
    · exact Or.inl h
    · exact Or.inr ⟨hw, by rwa [hS.interior_eq]⟩
  set U : Set Plane := D \ K with hUdef
  have hUopen : IsOpen U := hDo.sdiff hKclosed
  set A : Set Plane := Ω₁ ∪ Ω₂ with hAdef
  have hAopen : IsOpen A := hΩ₁o.union hΩ₂o
  have hΩ₁K : Disjoint Ω₁ K := by
    refine Set.disjoint_left.2 fun w hw hwK => ?_
    have : w ∈ frontier Ω₁ := by rw [hfΩ₁]; exact Or.inl hwK
    exact (hΩ₁o.frontier_eq ▸ this).2 hw
  have hΩ₂K : Disjoint Ω₂ K := by
    refine Set.disjoint_left.2 fun w hw hwK => ?_
    have : w ∈ frontier Ω₂ := by rw [hfΩ₂]; exact Or.inl hwK
    exact (hΩ₂o.frontier_eq ▸ this).2 hw
  have hAU : A ⊆ U := by
    rintro w (hw | hw)
    · exact ⟨hΩ₁D hw, Set.disjoint_left.1 hΩ₁K hw⟩
    · exact ⟨hΩ₂D hw, Set.disjoint_left.1 hΩ₂K hw⟩
  -- `A` is closed in `U`
  have hAcl : ∀ w ∈ U, w ∈ closure A → w ∈ A := by
    intro w hw hwc
    rw [hAdef, closure_union] at hwc
    have hstep : ∀ (Ω G : Set Plane), IsOpen Ω → frontier Ω = K ∪ G → G ⊆ C →
        w ∈ closure Ω → w ∈ Ω := by
      intro Ω G hΩ hfΩ hGC hwΩ
      rcases hclosure Ω hΩ hwΩ with h | h
      · exact h
      · rw [hfΩ] at h
        rcases h with h | h
        · exact absurd h hw.2
        · exact absurd (hGC h) (Set.disjoint_left.1 hDC hw.1)
    have hG₁C : G₁ ⊆ C := by rw [← hG]; exact subset_union_left
    have hG₂C : G₂ ⊆ C := by rw [← hG]; exact subset_union_right
    rcases hwc with h | h
    · exact Or.inl (hstep Ω₁ G₁ hΩ₁o hfΩ₁ hG₁C h)
    · exact Or.inr (hstep Ω₂ G₂ hΩ₂o hfΩ₂ hG₂C h)
  intro x hx
  by_contra hxA
  have hxcl : x ∉ closure A := fun h => hxA (hAcl x hx h)
  set V : Set Plane := connectedComponentIn U x with hVdef
  have hxV : x ∈ V := mem_connectedComponentIn hx
  have hVU : V ⊆ U := connectedComponentIn_subset U x
  have hVconn : IsPreconnected V := isPreconnected_connectedComponentIn
  -- `V` misses `A`
  have hVA : Disjoint V A := by
    have hcover : V ⊆ A ∪ (U ∩ (closure A)ᶜ) := by
      intro w hw
      by_cases h : w ∈ closure A
      · exact Or.inl (hAcl w (hVU hw) h)
      · exact Or.inr ⟨hVU hw, h⟩
    have hdis : Disjoint A (U ∩ (closure A)ᶜ) :=
      Set.disjoint_left.2 fun u hu hu' => hu'.2 (subset_closure hu)
    have := hVconn.subset_right_of_subset_union hAopen
      (hUopen.inter isClosed_closure.isOpen_compl) hdis hcover ⟨x, hxV, hx, hxcl⟩
    exact Set.disjoint_left.2 fun u hu hu' => (this hu).2 (subset_closure hu')
  -- the frontier of `V` lies on the curve or on `K`
  have hfrU : frontier U ⊆ C ∪ K := by
    have h : U = D ∩ Kᶜ := by rw [hUdef, Set.sdiff_eq]
    rw [h]
    refine (frontier_inter_subset D Kᶜ).trans ?_
    rintro w (hw | hw)
    · exact Or.inl (hfrD ▸ hw.1)
    · refine Or.inr ?_
      have := hw.2
      rw [frontier_compl] at this
      exact hKclosed.frontier_subset this
  have hfrV : frontier V ⊆ C ∪ K :=
    (frontier_connectedComponentIn_subset hUopen).trans hfrU
  by_cases hcase : ∃ y ∈ frontier V, y ∈ C ∧ y ∉ K
  · -- the local connectedness of `D` at such a frontier point gives the contradiction
    obtain ⟨y, hyfr, hyC, hyK⟩ := hcase
    obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKclosed.isOpen_compl y hyK
    obtain ⟨δ, hδ, hjoin⟩ := hlc y hyC ρ hρ
    set δ' := min δ ρ with hδ'
    have hδ'pos : 0 < δ' := lt_min hδ hρ
    obtain ⟨p, hpV, hpd⟩ := Metric.mem_closure_iff.1 hyfr.1 δ' hδ'pos
    have hyΩ : ∃ Ω, (Ω = Ω₁ ∨ Ω = Ω₂) ∧ y ∈ closure Ω := by
      have : y ∈ G₁ ∪ G₂ := by rw [hG]; exact hyC
      rcases this with h | h
      · exact ⟨Ω₁, Or.inl rfl, frontier_subset_closure (by rw [hfΩ₁]; exact Or.inr h)⟩
      · exact ⟨Ω₂, Or.inr rfl, frontier_subset_closure (by rw [hfΩ₂]; exact Or.inr h)⟩
    obtain ⟨Ω, hΩcase, hycl⟩ := hyΩ
    obtain ⟨q, hqΩ, hqd⟩ := Metric.mem_closure_iff.1 hycl δ' hδ'pos
    have hqA : q ∈ A := by rcases hΩcase with rfl | rfl; exacts [Or.inl hqΩ, Or.inr hqΩ]
    have hqD : q ∈ D := by rcases hΩcase with rfl | rfl; exacts [hΩ₁D hqΩ, hΩ₂D hqΩ]
    have hpD : p ∈ D := (hVU hpV).1
    have hpball : p ∈ ball y δ := by
      rw [mem_ball, dist_comm]
      exact lt_of_lt_of_le hpd (min_le_left δ ρ)
    have hqball : q ∈ ball y δ := by
      rw [mem_ball, dist_comm]
      exact lt_of_lt_of_le hqd (min_le_left δ ρ)
    have hjoined := hjoin p ⟨hpD, hpball⟩ q ⟨hqD, hqball⟩
    have hsub : D ∩ ball y ρ ⊆ U := by
      rintro w ⟨hwD, hwball⟩
      exact ⟨hwD, hρK hwball⟩
    have hqcomp : q ∈ connectedComponentIn U p :=
      connectedComponentIn_mono p hsub (mem_connectedComponentIn_of_joinedIn hjoined)
    rw [← connectedComponentIn_eq hpV] at hqcomp
    exact (Set.disjoint_left.1 hVA) hqcomp hqA
  · -- otherwise the frontier of `V` lies in `K`, so `V` is the whole complement of `K`
    push Not at hcase
    have hfrVK : frontier V ⊆ K := by
      intro w hw
      rcases hfrV hw with h | h
      · exact hcase w hw h
      · exact h
    have hVK : V ⊆ Kᶜ := fun w hw => (hVU hw).2
    have hcover : Kᶜ ⊆ V ∪ (closure V)ᶜ := by
      intro w hw
      by_cases h : w ∈ closure V
      · rcases hclosure V (hUopen.connectedComponentIn) h with h' | h'
        · exact Or.inl h'
        · exact absurd (hfrVK h') hw
      · exact Or.inr h
    have hdis : Disjoint V ((closure V)ᶜ) :=
      Set.disjoint_left.2 fun u hu hu' => hu' (subset_closure hu)
    have hKV : Kᶜ ⊆ V :=
      hKcompl.subset_left_of_subset_union (hUopen.connectedComponentIn)
        isClosed_closure.isOpen_compl hdis hcover ⟨x, hVK hxV, hxV⟩
    obtain ⟨y, hyC, hyK⟩ := hCK
    exact (Set.disjoint_left.1 hDC) (hVU (hKV hyK)).1 hyC

/-- **Local absorption by a crosscut domain.**

Let `D` be an open set disjoint from the curve `C`, let `Ω ⊆ D` be open with
`frontier Ω = K ∪ G`, where `K` is closed and `G ⊆ C` (in the application, `Ω` is the domain
cut off by a crosscut `K` of `D` along the arc `G` of `C`), and let `y` be a point of
`closure Ω` at which `D` is locally connected and around which a ball of radius `ρ` misses
`K`.  Then all points of `D` close enough to `y` already lie in `Ω`.

This is the local form of the θ-curve theorem, and the only form of it that the construction
of the neighbourhoods `U` of the local part of Theorem 4 of
Klein–Langetepe–Nilforoushan (2009) needs.  Contrary to `AVD.crosscut_exhausts`, it does not
require a second crosscut domain, so it applies verbatim to the unbounded curves of axiom
`A₁`, for which the complement of the small arc in the curve is not an arc. -/
theorem exists_ball_inter_subset {D C K G Ω : Set Plane} (hDo : IsOpen D)
    (hDC : Disjoint D C) (hKclosed : IsClosed K)
    (hΩo : IsOpen Ω) (hΩD : Ω ⊆ D) (hfΩ : frontier Ω = K ∪ G) (hGC : G ⊆ C)
    {y : Plane} (hlc : LocallyConnectedAt D y) (hycl : y ∈ closure Ω)
    {ρ : ℝ} (hρ : 0 < ρ) (hballK : Disjoint (ball y ρ) K) :
    ∃ ρ' > 0, ρ' ≤ ρ ∧ ball y ρ' ∩ D ⊆ Ω := by
  have hclosure : ∀ S : Set Plane, IsOpen S → closure S ⊆ S ∪ frontier S := by
    intro S hS w hw
    by_cases h : w ∈ S
    · exact Or.inl h
    · exact Or.inr ⟨hw, by rwa [hS.interior_eq]⟩
  have hΩK : Disjoint Ω K := by
    refine Set.disjoint_left.2 fun w hw hwK => ?_
    have : w ∈ frontier Ω := by rw [hfΩ]; exact Or.inl hwK
    exact (hΩo.frontier_eq ▸ this).2 hw
  set U : Set Plane := D \ K with hUdef
  have hUopen : IsOpen U := hDo.sdiff hKclosed
  have hΩU : Ω ⊆ U := fun w hw => ⟨hΩD hw, Set.disjoint_left.1 hΩK hw⟩
  have hΩclosedU : ∀ w ∈ U, w ∈ closure Ω → w ∈ Ω := by
    intro w hw hwc
    rcases hclosure Ω hΩo hwc with h | h
    · exact h
    · rw [hfΩ] at h
      rcases h with h | h
      · exact absurd h hw.2
      · exact absurd (hGC h) (Set.disjoint_left.1 hDC hw.1)
  obtain ⟨δ, hδ, hjoin⟩ := hlc ρ hρ
  have hρ'pos : 0 < min δ ρ := lt_min hδ hρ
  refine ⟨min δ ρ, hρ'pos, min_le_right _ _, ?_⟩
  rintro x ⟨hxb, hxD⟩
  obtain ⟨q, hqΩ, hqd⟩ := Metric.mem_closure_iff.1 hycl (min δ ρ) hρ'pos
  have hqball : q ∈ ball y δ := by
    rw [mem_ball, dist_comm]
    exact lt_of_lt_of_le hqd (min_le_left _ _)
  have hjoined : JoinedIn (D ∩ ball y ρ) q x :=
    (hjoin x ⟨hxD, ball_subset_ball (min_le_left δ ρ) hxb⟩ q ⟨hΩD hqΩ, hqball⟩).symm
  have hsub : D ∩ ball y ρ ⊆ U := by
    rintro w ⟨hwD, hwb⟩
    exact ⟨hwD, Set.disjoint_left.1 hballK hwb⟩
  have hxcomp : x ∈ connectedComponentIn U q :=
    connectedComponentIn_mono q hsub (mem_connectedComponentIn_of_joinedIn hjoined)
  -- the component of `q` in `D ∖ K` lies in `Ω`, which is open and closed in `D ∖ K`
  have hVsub : connectedComponentIn U q ⊆ Ω := by
    have hcover : connectedComponentIn U q ⊆ Ω ∪ (U ∩ (closure Ω)ᶜ) := by
      intro w hw
      by_cases h : w ∈ closure Ω
      · exact Or.inl (hΩclosedU w (connectedComponentIn_subset U q hw) h)
      · exact Or.inr ⟨connectedComponentIn_subset U q hw, h⟩
    have hdis : Disjoint Ω (U ∩ (closure Ω)ᶜ) :=
      Set.disjoint_left.2 fun v hv hv' => hv'.2 (subset_closure hv)
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hΩo
      (hUopen.inter isClosed_closure.isOpen_compl) hdis hcover
      ⟨q, mem_connectedComponentIn (hΩU hqΩ), hqΩ⟩
  exact hVsub hxcomp

end AVD
