import AbstractVoronoi.Jordan.LocalStructure

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
`NoPlaneEmbeddingK33`, and *proves* it from the corresponding result of the Jordan curve
theorem development this project depends on
(`JordanCurveTheorem.no_k33_planar_graph_data`, itself a consequence of the non-planarity
of `K₃,₃` proved there).  The paper cites for it C. Thomassen, *The converse of the Jordan
curve theorem and a characterization of planar maps*, Geometriae Dedicata 32 (1989) 53–57.
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

It is deduced here from `Graph.IsArcK33.elim` of the Jordan–Schönflies development this
project depends on: that result says that nine arcs of the plane joining three points
`x₀, x₁, x₂` to three points `y₀, y₁, y₂` and meeting only at shared endpoints cannot
exist, which is exactly the configuration forbidden here. -/
theorem noPlaneEmbeddingK33 : NoPlaneEmbeddingK33 := by
  intro v a α hv ha harc h0 h1 hdisj hvi haj
  set P : Fin 3 → Fin 3 → Set Plane := fun i j => α i j '' Icc 0 1 with hPdef
  -- the nine arcs, in the set form of the Jordan–Schönflies development
  have harcb : ∀ i j, Schoenflies.IsArcBetween (P i j) (v i) (a j) := by
    intro i j
    have h := (harc i j).isArcBetween
    rwa [h0 i j, h1 i j] at h
  have hmem0 : ∀ i j, v i ∈ P i j := by
    intro i j
    exact ⟨0, ⟨le_refl 0, zero_le_one⟩, h0 i j⟩
  have hmem1 : ∀ i j, a j ∈ P i j := by
    intro i j
    exact ⟨1, ⟨zero_le_one, le_refl 1⟩, h1 i j⟩
  -- the two sides of the bipartition are disjoint: an arc has distinct endpoints
  have hne : ∀ i j, v i ≠ a j := by
    intro i j hij
    have h01 : α i j 0 = α i j 1 := by rw [h0 i j, h1 i j, hij]
    have h := (harc i j).inj (mem_Icc.2 ⟨le_refl 0, zero_le_one⟩)
      (mem_Icc.2 ⟨zero_le_one, le_refl 1⟩) h01
    norm_num at h
  refine Graph.IsArcK33.elim (x := v) (y := a) (P := P) ⟨harcb, hv, ha, hne, ?_⟩
  -- two distinct arcs meet only in a common endpoint
  intro i j k l hik u hu
  by_cases hi : i = k
  · subst hi
    have hjl : j ≠ l := fun h => hik (by rw [h])
    have hval : u = v i := (hvi i j l hjl).subset hu
    exact ⟨Or.inl hval, Or.inl hval⟩
  · by_cases hj : j = l
    · subst hj
      have hval : u = a j := (haj i k j hi).subset hu
      exact ⟨Or.inr hval, Or.inr hval⟩
    · exact absurd (Set.disjoint_left.1 (hdisj i k j l hi hj) hu.1) (fun h => h hu.2)

end AVD
