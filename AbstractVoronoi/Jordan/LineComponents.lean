import AbstractVoronoi.Imports

/-!
# Open subsets of the line with finite boundary

An open subset of the real line whose frontier is finite has only finitely many connected
components.  This elementary fact is the counting device behind the proof of **Theorem 10**
of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902:

the Voronoi edges lying on one bisecting curve `J(p,q)` are the connected components of a
relatively open subset of that curve whose boundary points are Voronoi vertices, of which
there are only finitely many by Lemma 9.
-/

noncomputable section

open Set Topology

namespace AVD

/-- The components of an open subset `X` of the line are open and order-connected, and a
finite infimum of a component is a boundary point of `X`. -/
theorem sInf_connectedComponentIn_mem_frontier {X : Set ℝ} (hX : IsOpen X) {x : ℝ}
    (hx : x ∈ X) (hbdd : BddBelow (connectedComponentIn X x)) :
    sInf (connectedComponentIn X x) ∈ frontier X := by
  set I := connectedComponentIn X x with hIdef
  have hxI : x ∈ I := mem_connectedComponentIn hx
  have hIsub : I ⊆ X := connectedComponentIn_subset X x
  have hne : I.Nonempty := ⟨x, hxI⟩
  set a := sInf I with hadef
  have hcl : a ∈ closure X := closure_mono hIsub (csInf_mem_closure hne hbdd)
  have hnot : a ∉ X := by
    intro haX
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hX a haX
    have hJ : Ioo (a - ε) (a + ε) ⊆ X := by
      rw [← Real.ball_eq_Ioo]; exact hball
    -- a point of `I` close to its infimum
    obtain ⟨y, hyI, hy⟩ := exists_lt_of_csInf_lt hne (show a < a + ε by linarith)
    have hya : a ≤ y := csInf_le hbdd hyI
    have hymem : y ∈ Ioo (a - ε) (a + ε) := ⟨by linarith, hy⟩
    have hunion : IsPreconnected (Ioo (a - ε) (a + ε) ∪ I) :=
      IsPreconnected.union y hymem hyI isPreconnected_Ioo isPreconnected_connectedComponentIn
    have hsub : Ioo (a - ε) (a + ε) ∪ I ⊆ X := union_subset hJ hIsub
    have := hunion.subset_connectedComponentIn (Or.inr hxI) hsub
    have hmem : a - ε / 2 ∈ I := this (Or.inl ⟨by linarith, by linarith⟩)
    have : a ≤ a - ε / 2 := csInf_le hbdd hmem
    linarith
  rw [hX.frontier_eq]
  exact ⟨hcl, hnot⟩

/-- An open connected subset `I` of the line is an interval, so its frontier is contained in
the pair `{sInf I, sSup I}` of its two possible finite ends.

This is what bounds by two the number of ends of an edge of a plane graph. -/
theorem frontier_subset_pair_of_ordConnected {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) : frontier I ⊆ {sInf I, sSup I} := by
  intro t ht
  have htc : t ∈ closure I := ht.1
  have htn : t ∉ I := by
    have h := ht.2
    rwa [hI.interior_eq] at h
  have hne : I.Nonempty := closure_nonempty_iff.1 ⟨t, htc⟩
  rcases em (∀ x ∈ I, t ≤ x) with hlow | hlow
  · -- `t` bounds `I` from below and lies in its closure, hence `t = sInf I`
    left
    have hbdd : BddBelow I := ⟨t, hlow⟩
    have hcl : closure I ⊆ Set.Ici (sInf I) :=
      closure_minimal (fun x hx => csInf_le hbdd hx) isClosed_Ici
    exact le_antisymm (le_csInf hne hlow) (hcl htc)
  · -- otherwise some point of `I` lies below `t`; since `I` is an interval missing `t`,
    -- the point `t` bounds `I` from above, hence `t = sSup I`
    right
    obtain ⟨x, hxI, hxt⟩ : ∃ x ∈ I, x < t := by
      by_contra hc
      exact hlow fun x hx => not_lt.1 fun h => hc ⟨x, hx, h⟩
    have hup : ∀ y ∈ I, y ≤ t := by
      intro y hyI
      by_contra hcon
      exact htn (hord.out hxI hyI ⟨hxt.le, (not_le.1 hcon).le⟩)
    have hbdd : BddAbove I := ⟨t, hup⟩
    have hcl : closure I ⊆ Set.Iic (sSup I) :=
      closure_minimal (fun y hy => le_csSup hbdd hy) isClosed_Iic
    exact le_antisymm (hcl htc) (csSup_le hne hup)

/-- An open connected subset of the line has a **finite frontier**: at most its two finite
ends. -/
theorem frontier_finite_of_ordConnected {I : Set ℝ} (hI : IsOpen I) (hord : I.OrdConnected) :
    (frontier I).Finite :=
  Set.Finite.subset (Set.toFinite _) (frontier_subset_pair_of_ordConnected hI hord)

/-- An open connected subset of the line has **at most two ends**: its frontier has at most
two points. -/
theorem frontier_ncard_le_two_of_ordConnected {I : Set ℝ} (hI : IsOpen I)
    (hord : I.OrdConnected) : (frontier I).ncard ≤ 2 := by
  calc (frontier I).ncard ≤ ({sInf I, sSup I} : Set ℝ).ncard :=
        Set.ncard_le_ncard (frontier_subset_pair_of_ordConnected hI hord) (Set.toFinite _)
    _ ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp [Set.ncard_singleton]

/-- The ends of a connected component of an open subset of the line — the points of its
closure that do not belong to it — are frontier points of the set.

This is what makes the endpoints of a Voronoi edge into Voronoi vertices. -/
theorem closure_connectedComponentIn_diff_subset_frontier {X : Set ℝ} (hX : IsOpen X)
    {x : ℝ} (hx : x ∈ X) :
    closure (connectedComponentIn X x) \ connectedComponentIn X x ⊆ frontier X := by
  set I := connectedComponentIn X x with hIdef
  rintro t ⟨htcl, htn⟩
  have htX : t ∉ X := by
    intro htX
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hX t htX
    obtain ⟨y, hyI, hy⟩ := Metric.mem_closure_iff.1 htcl ε hε
    have hyball : y ∈ Metric.ball t ε := Metric.mem_ball'.2 hy
    have hpre : IsPreconnected (Metric.ball t ε ∪ I) :=
      IsPreconnected.union y hyball hyI (convex_ball t ε).isPreconnected
        isPreconnected_connectedComponentIn
    have hsubX : Metric.ball t ε ∪ I ⊆ X :=
      union_subset hball (connectedComponentIn_subset X x)
    have hsub := hpre.subset_connectedComponentIn (Or.inr (mem_connectedComponentIn hx)) hsubX
    exact htn (hsub (Or.inl (Metric.mem_ball_self hε)))
  refine ⟨closure_mono (connectedComponentIn_subset X x) htcl, ?_⟩
  rw [hX.interior_eq]
  exact htX

/-- The connected components of an open subset `X` of the line are encoded injectively by
their infimum: a component bounded below is sent to its infimum, which is a frontier point
of `X`, and the (at most one) component unbounded below is sent to `none`.

This is the counting device behind `AVD.finite_components_of_finite_frontier` and
`AVD.ncard_components_le_frontier`. -/
theorem exists_components_encoding {X : Set ℝ} (hX : IsOpen X) :
    ∃ f : Set ℝ → Option ℝ,
      InjOn f {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x} ∧
        f '' {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x} ⊆
          insert none (some '' frontier X) := by
  classical
  set comps : Set (Set ℝ) := {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x} with hcomps
  -- the encoding of a component by its infimum
  set f : Set ℝ → Option ℝ := fun I => if BddBelow I then some (sInf I) else none with hfdef
  have hord : ∀ I ∈ comps, I.OrdConnected := by
    rintro I ⟨x, -, rfl⟩
    exact isPreconnected_connectedComponentIn.ordConnected
  have hsubX : ∀ I ∈ comps, I ⊆ X := by
    rintro I ⟨x, -, rfl⟩
    exact connectedComponentIn_subset X x
  have hne : ∀ I ∈ comps, I.Nonempty := by
    rintro I ⟨x, hx, rfl⟩
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hcomp_eq : ∀ I ∈ comps, ∀ y ∈ I, I = connectedComponentIn X y := by
    rintro I ⟨x, -, rfl⟩ y hy
    exact connectedComponentIn_eq hy
  -- a bounded component has its infimum on the frontier, in particular outside `X`
  have hinf : ∀ I ∈ comps, BddBelow I → sInf I ∈ frontier X := by
    rintro I ⟨x, hx, rfl⟩ hbdd
    exact sInf_connectedComponentIn_mem_frontier hX hx hbdd
  have hinfnot : ∀ I ∈ comps, BddBelow I → sInf I ∉ I := by
    intro I hI hbdd hmem
    have h1 : sInf I ∈ frontier X := hinf I hI hbdd
    rw [hX.frontier_eq] at h1
    exact h1.2 (hsubX I hI hmem)
  -- the encoding is injective
  have hinjOn : InjOn f comps := by
    intro I hI I' hI' hff
    simp only [hfdef] at hff
    have hIne := hne I hI
    have hI'ne := hne I' hI'
    have key : ∃ y, y ∈ I ∧ y ∈ I' := by
      by_cases hb : BddBelow I <;> by_cases hb' : BddBelow I'
      · rw [ite_eq_left hb, ite_eq_left hb'] at hff
        have heq : sInf I = sInf I' := Option.some_injective ℝ hff
        obtain ⟨x, hx⟩ := hIne
        have hxa : sInf I < x := by
          rcases eq_or_lt_of_le (csInf_le hb hx) with h | h
          · exact absurd (by rw [h]; exact hx) (hinfnot I hI hb)
          · exact h
        obtain ⟨y, hyI', hyx⟩ := exists_lt_of_csInf_lt hI'ne (by rw [← heq]; exact hxa)
        have hya : sInf I ≤ y := by rw [heq]; exact csInf_le hb' hyI'
        have hyne : sInf I ≠ y := by
          intro h
          refine hinfnot I' hI' hb' ?_
          rw [← heq, h]
          exact hyI'
        obtain ⟨z, hzI, hzy⟩ := exists_lt_of_csInf_lt (hne I hI) (lt_of_le_of_ne hya hyne)
        refine ⟨y, ?_, hyI'⟩
        exact (hord I hI).out hzI hx ⟨le_of_lt hzy, le_of_lt hyx⟩
      · rw [ite_eq_left hb, ite_eq_right hb'] at hff
        exact absurd hff (by simp)
      · rw [ite_eq_right hb, ite_eq_left hb'] at hff
        exact absurd hff (by simp)
      · obtain ⟨x, hx⟩ := hIne
        obtain ⟨x', hx'⟩ := hI'ne
        rcases le_total x x' with hle | hle
        · -- `x ∈ I'`, since `I'` is unbounded below and contains `x'`
          obtain ⟨y', hy'I', hy'x⟩ : ∃ y' ∈ I', y' < x := by
            by_contra hcon
            push Not at hcon
            exact hb' ⟨x, fun y hy => hcon y hy⟩
          exact ⟨x, hx, (hord I' hI').out hy'I' hx' ⟨le_of_lt hy'x, hle⟩⟩
        · obtain ⟨y, hyI, hyx⟩ : ∃ y ∈ I, y < x' := by
            by_contra hcon
            push Not at hcon
            exact hb ⟨x', fun y hy => hcon y hy⟩
          exact ⟨x', (hord I hI).out hyI hx ⟨le_of_lt hyx, hle⟩, hx'⟩
    obtain ⟨y, hyI, hyI'⟩ := key
    rw [hcomp_eq I hI y hyI, hcomp_eq I' hI' y hyI']
  -- the image of the encoding is finite
  have himg : f '' comps ⊆ insert none (some '' frontier X) := by
    rintro u ⟨I, hI, rfl⟩
    by_cases hb : BddBelow I
    · refine Or.inr ⟨sInf I, hinf I hI hb, ?_⟩
      rw [hfdef]; simp [hb]
    · left
      rw [hfdef]; simp [hb]
  exact ⟨f, hinjOn, himg⟩

/-- An open subset of the real line whose frontier is finite has only finitely many
connected components. -/
theorem finite_components_of_finite_frontier {X : Set ℝ} (hX : IsOpen X)
    (hF : (frontier X).Finite) :
    {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x}.Finite := by
  obtain ⟨f, hinjOn, himg⟩ := exists_components_encoding hX
  have hfin : (f '' {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x}).Finite :=
    ((hF.image some).insert none).subset himg
  exact Set.Finite.of_finite_image hfin hinjOn

/-- The quantitative form of `AVD.finite_components_of_finite_frontier`: an open subset of
the real line has at most one more connected component than it has frontier points.

This is what turns the finiteness of the set of Voronoi vertices into an explicit bound on
the number of Voronoi edges lying on one bisecting curve. -/
theorem ncard_components_le_frontier {X : Set ℝ} (hX : IsOpen X)
    (hF : (frontier X).Finite) :
    {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x}.ncard ≤ (frontier X).ncard + 1 := by
  obtain ⟨f, hinjOn, himg⟩ := exists_components_encoding hX
  have hfin : (insert none (some '' frontier X)).Finite := (hF.image some).insert none
  calc {I : Set ℝ | ∃ x ∈ X, I = connectedComponentIn X x}.ncard
      ≤ (insert none (some '' frontier X)).ncard :=
        Set.ncard_le_ncard_of_injOn f (fun I hI => himg ⟨I, hI, rfl⟩) hinjOn hfin
    _ ≤ (some '' frontier X).ncard + 1 := Set.ncard_insert_le _ _
    _ = (frontier X).ncard + 1 := by
        rw [Set.ncard_image_of_injective _ (Option.some_injective ℝ)]

end AVD
