import AbstractVoronoi.Jordan.LocalStructure
import AbstractVoronoi.Jordan.CrosscutSplit
import AbstractVoronoi.Jordan.Backend

/-!
# The complete bipartite graph `K₃,₃` has no plane embedding

The proof of Lemma 9 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

uses "the following elegant argument of Thomassen's":

> In each Voronoi region `VR(p_j, S)` we choose a point denoted by `a_j`.  Now suppose, by
> way of contradiction, that `B` contains three different points, `v₁, v₂, v₃`.  By Lemma 8
> and axiom `A₂`, we can find arcs `α_{i,j}` connecting `v_i` to `a_j`, such that
> `α_{i,j} \ {v_i}` is fully contained in `VR(p_j, S)`.  We may even assume that for each
> `j`, the three arcs `α_{1,j}, α_{2,j}, α_{3,j}` contained in the region of `p_j` form a
> plane tree `T_j` rooted at `a_j`.  Since the Voronoi regions of `p₁, p₂, p₃` are disjoint,
> the trees `T₁, T₂, T₃` are realizing a plane embedding of the bipartite graph `K₃,₃`,
> which is impossible.

This file isolates the classical graph-theoretic fact used there — *the complete bipartite
graph `K₃,₃` has no plane embedding* — as a single explicit statement,
`NoPlaneEmbeddingK33`, and *proves* it in this project from the Jordan–Schönflies theorem
(through the local connectedness of the complementary domains of a closed Jordan curve,
`AVD.IsClosedJordanCurve.locallyConnectedAt`) and the θ-curve theorem
(`AVD.exists_crosscut_domains`, `AVD.crosscut_exhausts`).  The paper cites for it
C. Thomassen, *The converse of the Jordan curve theorem and a characterization of planar
maps*, Geometriae Dedicata 32 (1989) 53–57.

The argument is the classical one.  The four edges `v₀a₀, a₀v₁, v₁a₁, a₁v₀` form a closed
Jordan curve `C`, and the path `a₀ v₂ a₁` is a crosscut `κ` of the complementary domain `D`
of `C` containing `v₂`.  By the θ-curve theorem, `κ` cuts `D` into two domains `Ω₀, Ω₁`,
where `Ωᵢ` is bounded by `κ` and the path `a₀ vᵢ a₁`.  The edge `v₂a₂` puts `a₂` into
`D ∖ κ`, hence into some `Ωᵢ`; the edge `a₂v₁₋ᵢ` then stays inside `Ωᵢ` up to its endpoint
`v₁₋ᵢ`, which therefore lies on the frontier of `Ωᵢ`, which it does not.
-/

noncomputable section

open Set Topology

namespace AVD

/-- **`K₃,₃` has no plane embedding**, stated as a proposition.

A plane embedding of the complete bipartite graph `K₃,₃` consists of two triples of pairwise
distinct points `v₀, v₁, v₂` and `a₀, a₁, a₂` of the plane, together with nine arcs
`α i j` joining `v i` to `a j`, such that two arcs meet only in the vertices they share:
two arcs with no vertex in common are disjoint, two arcs sharing the vertex `v i` meet
exactly in `v i`, and two arcs sharing the vertex `a j` meet exactly in `a j`.

`NoPlaneEmbeddingK33` states that no such configuration exists. -/
def NoPlaneEmbeddingK33 : Prop :=
  ∀ (v a : Fin 3 → Plane) (α : Fin 3 → Fin 3 → (ℝ → Plane)),
    Function.Injective v → Function.Injective a →
    (∀ i j, IsArc (α i j)) →
    (∀ i j, α i j 0 = v i) → (∀ i j, α i j 1 = a j) →
    (∀ i i' j j', i ≠ i' → j ≠ j' →
      Disjoint (α i j '' Icc 0 1) (α i' j' '' Icc 0 1)) →
    (∀ i j j', j ≠ j' → α i j '' Icc 0 1 ∩ α i j' '' Icc 0 1 = {v i}) →
    (∀ i i' j, i ≠ i' → α i j '' Icc 0 1 ∩ α i' j '' Icc 0 1 = {a j}) →
    False

/-- **`K₃,₃` has no plane embedding.**

This is the classical fact used, via Thomassen's argument, in the proof of Lemma 9 of
Klein–Langetepe–Nilforoushan (2009); the paper cites C. Thomassen, *The converse of the
Jordan curve theorem and a characterization of planar maps*, Geometriae Dedicata 32 (1989)
53–57.

It is proved here from the Jordan–Schönflies theorem and the θ-curve theorem, by the
classical argument recalled in the module docstring: the cycle `v₀ a₀ v₁ a₁` is a closed
Jordan curve, the path `a₀ v₂ a₁` is a crosscut of the complementary domain containing `v₂`,
and the edges `v₂a₂`, `a₂v₀`, `a₂v₁` cannot all be placed in the two domains it cuts off. -/
theorem noPlaneEmbeddingK33 : NoPlaneEmbeddingK33 := by
  intro v a α _ _ hα h0 h1 hdisj hvv haa
  obtain ⟨A, hA⟩ : ∃ A : Fin 3 → Fin 3 → Set Plane, ∀ i j, α i j '' Icc 0 1 = A i j :=
    ⟨_, fun _ _ => rfl⟩
  simp only [hA] at hdisj hvv haa
  have hvA : ∀ i j, v i ∈ A i j := fun i j => hA i j ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, h0 i j⟩
  have haA : ∀ i j, a j ∈ A i j := fun i j => hA i j ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, h1 i j⟩
  have hva : ∀ i j, v i ≠ a j := fun i j h => by
    have := (hα i j).inj ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ (by rw [h0, h1, h])
    norm_num at this
  -- two edges meet only in a common vertex
  have key : ∀ {x : Plane} {i j i' j' : Fin 3}, x ∈ A i j → x ∈ A i' j' →
      (i = i' ∧ j = j') ∨ (i = i' ∧ x = v i) ∨ (j = j' ∧ x = a j) := by
    intro x i j i' j' h h'
    by_cases hi : i = i'
    · subst hi
      by_cases hj : j = j'
      · exact Or.inl ⟨rfl, hj⟩
      · have hx : x ∈ A i j ∩ A i j' := ⟨h, h'⟩
        rw [hvv i j j' hj] at hx
        exact Or.inr (Or.inl ⟨rfl, hx⟩)
    · by_cases hj : j = j'
      · subst hj
        have hx : x ∈ A i j ∩ A i' j := ⟨h, h'⟩
        rw [haa i i' j hi] at hx
        exact Or.inr (Or.inr ⟨rfl, hx⟩)
      · exact absurd h' (Set.disjoint_left.1 (hdisj i i' j j' hi hj) h)
  have hvnot : ∀ {i i' j : Fin 3}, i ≠ i' → v i ∉ A i' j := by
    intro i i' j hii' h
    rcases key (hvA i j) h with h | h | h
    · exact hii' h.1
    · exact hii' h.1
    · exact hva i j h.2
  -- the three paths `a₀ – vᵢ – a₁`
  obtain ⟨P, hP⟩ : ∃ P : Fin 3 → ℝ → Plane,
      ∀ i, P i = concatParam (revParam (α i 0)) (α i 1) := ⟨_, fun _ => rfl⟩
  have hmid : ∀ i, revParam (α i 0) 1 = α i 1 0 := fun i => by rw [revParam_one, h0, h0]
  have hParc : ∀ i, IsArc (P i) := fun i => by
    rw [hP]
    refine (hα i 0).rev.concat (hα i 1) (hmid i) ?_
    rw [revParam_image, hA, hA, hvv i 0 1 (by decide), revParam_one, h0]
  have hP0 : ∀ i, P i 0 = a 0 := fun i => by rw [hP, concatParam_zero, revParam_zero, h1]
  have hP1 : ∀ i, P i 1 = a 1 := fun i => by rw [hP, concatParam_one, h1]
  have hPimg : ∀ i, P i '' Icc 0 1 = A i 0 ∪ A i 1 := fun i => by
    rw [hP, concatParam_image (hmid i), revParam_image, hA, hA]
  have hPIoo : ∀ i, ∀ x ∈ P i '' Ioo 0 1, (x ∈ A i 0 ∨ x ∈ A i 1) ∧ x ≠ a 0 ∧ x ≠ a 1 := by
    intro i x hx
    have h := (hParc i).image_Ioo_subset_diff hx
    rw [hPimg, hP0, hP1] at h
    exact ⟨h.1, fun h' => h.2 (Or.inl h'), fun h' => h.2 (Or.inr h')⟩
  -- two different paths meet only at `a₀` and `a₁`
  have hcross : ∀ {i i' : Fin 3}, i ≠ i' → ∀ x, (x ∈ A i 0 ∨ x ∈ A i 1) →
      (x ∈ A i' 0 ∨ x ∈ A i' 1) → x = a 0 ∨ x = a 1 := by
    intro i i' hii' x hx hx'
    rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;>
      rcases key hx hx' with h | h | h <;>
      first
        | exact absurd h.1 hii'
        | exact Or.inl h.2
        | exact Or.inr h.2
  have hint : Disjoint (P 0 '' Ioo 0 1) (P 1 '' Ioo 0 1) := by
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨hx, hxa0, hxa1⟩ := hPIoo 0 x hx
    rcases hcross (by decide) x hx (hPIoo 1 x hx').1 with h | h
    · exact hxa0 h
    · exact hxa1 h
  -- the 4-cycle `a₀ v₀ a₁ v₁` is a closed Jordan curve
  set C : Set Plane := P 0 '' Icc 0 1 ∪ P 1 '' Icc 0 1 with hCdef
  have hJ : IsClosedJordanCurve C :=
    isClosedJordanCurve_of_arcs (hParc 0) (hParc 1) (by rw [hP0, hP0]) (by rw [hP1, hP1]) hint
  have hCmem : ∀ {x}, x ∈ C → ∃ i j, i ≠ 2 ∧ j ≠ 2 ∧ x ∈ A i j := by
    intro x hx
    rw [hCdef, hPimg, hPimg] at hx
    rcases hx with (h | h) | (h | h)
    · exact ⟨0, 0, by decide, by decide, h⟩
    · exact ⟨0, 1, by decide, by decide, h⟩
    · exact ⟨1, 0, by decide, by decide, h⟩
    · exact ⟨1, 1, by decide, by decide, h⟩
  -- `v₂` lies off the cycle
  have hv2C : v 2 ∉ C := by
    intro hx
    obtain ⟨i, j, hi, -, hx⟩ := hCmem hx
    exact hvnot (Ne.symm hi) hx
  obtain ⟨D₁, D₂, h1o, h2o, h1c, h2c, hdisj12, hunion, hf1, hf2, -⟩ :=
    hJ.exists_separation_frontier_eq
  -- the main argument, in the complementary domain `D` of the cycle containing `v₂`
  have main : ∀ D E : Set Plane, IsOpen D → IsOpen E → IsConnected D → IsConnected E →
      Disjoint D E → D ∪ E = Cᶜ → frontier D = C → v 2 ∈ D → False := by
    intro D E hDo hEo hDc hEc hDE hDEu hfD hv2D
    have hDC : ∀ {x}, x ∈ D → x ∉ C := by
      intro x hx hxC
      exact (show x ∈ Cᶜ from hDEu ▸ Or.inl hx) hxC
    -- a connected set off the cycle meeting `D` lies in `D`
    have hsubD : ∀ S : Set Plane, IsPreconnected S → (∀ x ∈ S, x ∉ C) →
        ∀ y ∈ S, y ∈ D → S ⊆ D := by
      intro S hS hSC y hyS hyD
      rcases hS.subset_or_subset hDo hEo hDE (fun x hx => hDEu ▸ hSC x hx) with h | h
      · exact h
      · exact absurd (h hyS) (Set.disjoint_left.1 hDE hyD)
    -- the path `a₀ v₂ a₁` is a crosscut of `D`
    have hκD : P 2 '' Ioo 0 1 ⊆ D := by
      refine hsubD _ (isPreconnected_Ioo.image _ ((hParc 2).cont.mono Ioo_subset_Icc_self))
        ?_ (v 2) ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩ hv2D
      · intro x hx hxC
        obtain ⟨hx, hxa0, hxa1⟩ := hPIoo 2 x hx
        obtain ⟨i, j, hi, hj, hxij⟩ := hCmem hxC
        have hx' : x ∈ A i 0 ∨ x ∈ A i 1 := by
          rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
          · exact Or.inl hxij
          · exact Or.inr hxij
        rcases hcross (Ne.symm hi) x hx hx' with h | h
        · exact hxa0 h
        · exact hxa1 h
      · rw [hP, concatParam_of_le (by norm_num)]
        norm_num [revParam, h0]
    obtain ⟨Ω₁, Ω₂, hΩ1o, hΩ2o, -, -, hΩ12, hΩ1D, hΩ2D, -, -, hfr1, hfr2⟩ :=
      exists_crosscut_domains hDo hEo hDE hDEu (hParc 2) (hParc 0) (hParc 1)
        (by rw [hP0, hP0]) (by rw [hP1, hP1]) (by rw [hP0, hP0]) (by rw [hP1, hP1]) hκD rfl hint
    -- the θ-curve theorem: `Ω₁` and `Ω₂` exhaust `D ∖ κ`
    have hexh : D \ P 2 '' Icc 0 1 ⊆ Ω₁ ∪ Ω₂ := by
      refine crosscut_exhausts hDo hfD
        (isCompact_Icc.image_of_continuousOn (hParc 2).cont).isClosed
        (isPreconnected_compl_arc (hParc 2)) ⟨v 0, ?_, ?_⟩
        (fun y hy => hJ.locallyConnectedAt hDc hEc hDEu hy) hΩ1o hΩ2o hΩ1D hΩ2D hfr1 hfr2 rfl
      · rw [hCdef, hPimg]; exact Or.inl (Or.inl (hvA 0 0))
      · rw [hPimg]
        rintro (h | h) <;> exact hvnot (by decide) h
    -- the edge `v₂ a₂` lies in `D`, so `a₂ ∈ D ∖ κ`
    have hA22 : A 2 2 ⊆ D := by
      refine hsubD _ ?_ ?_ (v 2) (hvA 2 2) hv2D
      · rw [← hA]; exact isPreconnected_Icc.image _ (hα 2 2).cont
      · intro x hx hxC
        obtain ⟨i, j, hi, hj, hxij⟩ := hCmem hxC
        rcases key hx hxij with h | h | h
        · exact hi h.1.symm
        · exact hi h.1.symm
        · exact hj h.1.symm
    have ha2 : a 2 ∈ D \ P 2 '' Icc 0 1 := by
      refine ⟨hA22 (haA 2 2), ?_⟩
      rw [hPimg]
      rintro (h | h) <;> rcases key (haA 2 2) h with h' | h' | h'
      all_goals first
        | exact absurd h'.1 (by decide)
        | exact absurd h'.2 (by decide)
        | exact hva 2 2 h'.2.symm
    -- an edge `vᵢ a₂` with `i ≠ 2` forces `vᵢ` onto the frontier of the domain containing `a₂`
    have hfront : ∀ i, i ≠ 2 → ∀ Ω Ω' : Set Plane, IsOpen Ω → IsOpen Ω' → Disjoint Ω Ω' →
        Ω ⊆ D → D \ P 2 '' Icc 0 1 ⊆ Ω ∪ Ω' → a 2 ∈ Ω → v i ∈ frontier Ω := by
      intro i hi Ω Ω' hΩo hΩ'o hΩΩ' hΩD hcov ha2Ω
      set S : Set Plane := α i 2 '' Ioc 0 1 with hSdef
      have hSA : ∀ x ∈ S, ∀ i' j', j' ≠ 2 → x ∉ A i' j' := by
        rintro x ⟨t, ht, rfl⟩ i' j' hj' hx
        have hxA : α i 2 t ∈ A i 2 := hA i 2 ▸ ⟨t, Ioc_subset_Icc_self ht, rfl⟩
        rcases key hxA hx with h | h | h
        · exact hj' h.2.symm
        · have := (hα i 2).inj (Ioc_subset_Icc_self ht) ⟨le_rfl, zero_le_one⟩
            (by rw [h.2, h0])
          exact ht.1.ne' this
        · exact hj' h.1.symm
      have hSpre : IsPreconnected S :=
        isPreconnected_Ioc.image _ ((hα i 2).cont.mono Ioc_subset_Icc_self)
      have ha2S : a 2 ∈ S := ⟨1, ⟨zero_lt_one, le_rfl⟩, h1 i 2⟩
      have hSD : S ⊆ D := hsubD S hSpre (fun x hx hxC => by
        obtain ⟨i', j', -, hj', hx'⟩ := hCmem hxC
        exact hSA x hx i' j' hj' hx') (a 2) ha2S ha2.1
      have hSΩ : S ⊆ Ω := by
        have hSsub : S ⊆ Ω ∪ Ω' := fun x hx => hcov ⟨hSD hx, by
          rw [hPimg]
          rintro (h | h)
          · exact hSA x hx 2 0 (by decide) h
          · exact hSA x hx 2 1 (by decide) h⟩
        rcases hSpre.subset_or_subset hΩo hΩ'o hΩΩ' hSsub with h | h
        · exact h
        · exact absurd (h ha2S) (Set.disjoint_left.1 hΩΩ' ha2Ω)
      have hvcl : v i ∈ closure S := by
        have hcl : α i 2 '' closure (Ioc 0 1) ⊆ closure S :=
          ContinuousOn.image_closure (by rw [closure_Ioc zero_ne_one]; exact (hα i 2).cont)
        rw [closure_Ioc zero_ne_one] at hcl
        exact hcl ⟨0, ⟨le_rfl, zero_le_one⟩, h0 i 2⟩
      have hviC : v i ∈ C := by
        rw [hCdef, hPimg, hPimg]
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · exact Or.inl (Or.inl (hvA 0 0))
        · exact Or.inr (Or.inl (hvA 1 0))
      rw [hΩo.frontier_eq]
      exact ⟨closure_mono hSΩ hvcl, fun h => hDC (hΩD h) hviC⟩
    rcases hexh ha2 with h | h
    · have := hfront 1 (by decide) Ω₁ Ω₂ hΩ1o hΩ2o hΩ12 hΩ1D hexh h
      rw [hfr1, hPimg, hPimg] at this
      rcases this with (h | h) | (h | h) <;> exact hvnot (by decide) h
    · have := hfront 0 (by decide) Ω₂ Ω₁ hΩ2o hΩ1o hΩ12.symm hΩ2D
        (fun x hx => (hexh hx).symm) h
      rw [hfr2, hPimg, hPimg] at this
      rcases this with (h | h) | (h | h) <;> exact hvnot (by decide) h
  have hv2 : v 2 ∈ D₁ ∪ D₂ := hunion ▸ hv2C
  rcases hv2 with h | h
  · exact main D₁ D₂ h1o h2o h1c h2c hdisj12 hunion hf1 h
  · exact main D₂ D₁ h2o h1o h2c h1c hdisj12.symm (by rw [union_comm]; exact hunion) hf2 h

end AVD
