import AbstractVoronoi.Jordan.LocalStructure

/-!
# Two classical facts about arcs in the plane

Point-set topology about arcs that the paper

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902,

uses implicitly: two points accessible from an open path-connected set are joined by an arc
through that set (the three "Facts" in the proof of Lemma 6), the corresponding statement
for three points (the plane trees of footnote 10, used in Lemma 9), and the fact that two
arcs with common endpoints and disjoint relative interiors form a closed Jordan curve.
All of them are proved here.
-/

noncomputable section

open Set Topology

namespace AVD

/-- Two points that are accessible from an open, path-connected set `R` can be joined by an
arc whose relative interior lies in `R`.

This is the content of the three "Facts" in the proof of Lemma 6 of
Klein–Langetepe–Nilforoushan (2009): the access arcs of `a` and of `b` are concatenated
with a connection inside `R` (axiom `A₂`), cutting the pieces at their first mutual
intersection points.  The proof given here follows exactly that construction: the
connection inside `R` comes from `AVD.exists_arc_in_open` (an open connected plane set is
arcwise connected, footnote 5 of the paper) and the cutting is `AVD.exists_arc_cut`. -/
theorem exists_arc_of_accessible {R : Set Plane} (hopen : IsOpen R)
    (hconn : ∀ x ∈ R, ∀ y ∈ R, JoinedIn R x y) {a b : Plane} (hab : a ≠ b)
    (ha : AccessibleFrom R a) (hb : AccessibleFrom R b) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = a ∧ γ 1 = b ∧ γ '' Ioo 0 1 ⊆ R := by
  obtain ⟨α, hαarc, hα1, hαsub⟩ := ha
  obtain ⟨β, hβarc, hβ1, hβsub⟩ := hb
  have hp : α 0 ∈ R := hαsub ⟨0, ⟨le_refl 0, one_pos⟩, rfl⟩
  have hq : β 0 ∈ R := hβsub ⟨0, ⟨le_refl 0, one_pos⟩, rfl⟩
  have hpre : IsPreconnected R :=
    (IsPathConnected.isConnected ⟨α 0, hp, fun y hy => hconn _ hp y hy⟩).isPreconnected
  have hαimg : α '' Icc 0 1 ⊆ R ∪ {a} := by
    rw [← hα1]; exact image_Icc_subset_of_image_Ico hαsub
  have hβimg : β '' Icc 0 1 ⊆ R ∪ {b} := by
    rw [← hβ1]; exact image_Icc_subset_of_image_Ico hβsub
  by_cases haR : a ∈ R
  · by_cases hbR : b ∈ R
    · -- both points lie in `R`: an arc inside `R` will do
      obtain ⟨γ, hγ, h0, h1, hsub⟩ := exists_arc_in_open hopen hpre haR hbR hab
      exact ⟨γ, hγ, h0, h1, fun x hx => hsub (Set.image_mono Ioo_subset_Icc_self hx)⟩
    · -- only `b` lies outside `R`
      by_cases hqa : β 0 = a
      · exact ⟨β, hβarc, hqa, hβ1,
          fun x hx => hβsub (Set.image_mono Ioo_subset_Ico_self hx)⟩
      · obtain ⟨π, hπ, hπ0, hπ1, hπsub⟩ := exists_arc_in_open hopen hpre haR hq (Ne.symm hqa)
        have hbπ : b ∉ π '' Icc 0 1 := fun h => hbR (hπsub h)
        have h1' : revParam β 0 ∉ revParam π '' Icc 0 1 := by
          rw [revParam_zero, hβ1, revParam_image]; exact hbπ
        have h2' : revParam β 1 ∈ revParam π '' Icc 0 1 := by
          rw [revParam_one, revParam_image]; exact ⟨1, ⟨zero_le_one, le_refl 1⟩, hπ1⟩
        obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ := exists_arc_cut hβarc.rev hπ.rev h1' h2'
        have hg0 : revParam γ 0 = a := by rw [revParam_zero, hγ1, revParam_one, hπ0]
        have hg1 : revParam γ 1 = b := by rw [revParam_one, hγ0, revParam_zero, hβ1]
        refine ⟨revParam γ, hγ.rev, hg0, hg1, ?_⟩
        refine (hγ.rev).image_Ioo_subset_of_image_subset hg0 hg1 ?_
        rw [revParam_image]
        refine hγsub.trans ?_
        rw [revParam_image, revParam_image]
        rintro x (hx | hx)
        · rcases hβimg hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])
        · exact Or.inl (hπsub hx)
  · by_cases hbR : b ∈ R
    · -- only `a` lies outside `R`
      by_cases hpb : α 0 = b
      · refine ⟨revParam α, hαarc.rev, by rw [revParam_zero, hα1],
          by rw [revParam_one, hpb], ?_⟩
        rw [revParam_image_Ioo]
        exact fun x hx => hαsub (Set.image_mono Ioo_subset_Ico_self hx)
      · obtain ⟨π, hπ, hπ0, hπ1, hπsub⟩ := exists_arc_in_open hopen hpre hbR hp (Ne.symm hpb)
        -- `π` runs from `b` to `α 0` inside `R`
        have h1' : revParam α 0 ∉ revParam π '' Icc 0 1 := by
          rw [revParam_zero, hα1, revParam_image]
          exact fun h => haR (hπsub h)
        have h2' : revParam α 1 ∈ revParam π '' Icc 0 1 := by
          rw [revParam_one, revParam_image]; exact ⟨1, ⟨zero_le_one, le_refl 1⟩, hπ1⟩
        obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ := exists_arc_cut hαarc.rev hπ.rev h1' h2'
        have hg0 : γ 0 = a := by rw [hγ0, revParam_zero, hα1]
        have hg1 : γ 1 = b := by rw [hγ1, revParam_one, hπ0]
        refine ⟨γ, hγ, hg0, hg1, ?_⟩
        refine hγ.image_Ioo_subset_of_image_subset hg0 hg1 ?_
        refine hγsub.trans ?_
        rw [revParam_image, revParam_image]
        rintro x (hx | hx)
        · rcases hαimg hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])
        · exact Or.inl (hπsub hx)
    · -- both points lie outside `R`
      by_cases hpq : α 0 = β 0
      · have h1' : revParam α 0 ∉ β '' Icc 0 1 := by
          rw [revParam_zero, hα1]
          intro h
          rcases hβimg h with h' | h'
          · exact haR h'
          · rw [Set.mem_singleton_iff] at h'; exact hab h'
        have h2' : revParam α 1 ∈ β '' Icc 0 1 := by
          rw [revParam_one, hpq]; exact ⟨0, ⟨le_refl 0, zero_le_one⟩, rfl⟩
        obtain ⟨γ, hγ, hγ0, hγ1, hγsub⟩ := exists_arc_cut hαarc.rev hβarc h1' h2'
        have hg0 : γ 0 = a := by rw [hγ0, revParam_zero, hα1]
        have hg1 : γ 1 = b := by rw [hγ1, hβ1]
        refine ⟨γ, hγ, hg0, hg1, ?_⟩
        refine hγ.image_Ioo_subset_of_image_subset hg0 hg1 ?_
        refine hγsub.trans ?_
        rw [revParam_image]
        rintro x (hx | hx)
        · rcases hαimg hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])
        · rcases hβimg hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])
      · obtain ⟨π, hπ, hπ0, hπ1, hπsub⟩ := exists_arc_in_open hopen hpre hp hq hpq
        -- first cut: an arc from `a` to `β 0`
        have h1' : revParam α 0 ∉ π '' Icc 0 1 := by
          rw [revParam_zero, hα1]; exact fun h => haR (hπsub h)
        have h2' : revParam α 1 ∈ π '' Icc 0 1 := by
          rw [revParam_one]; exact ⟨0, ⟨le_refl 0, zero_le_one⟩, hπ0⟩
        obtain ⟨γ₁, hγ₁, hγ₁0, hγ₁1, hγ₁sub⟩ := exists_arc_cut hαarc.rev hπ h1' h2'
        have hγ₁0' : γ₁ 0 = a := by rw [hγ₁0, revParam_zero, hα1]
        have hγ₁img : γ₁ '' Icc 0 1 ⊆ R ∪ {a} := by
          refine hγ₁sub.trans ?_
          rw [revParam_image]
          rintro x (hx | hx)
          · exact hαimg hx
          · exact Or.inl (hπsub hx)
        -- second cut: an arc from `b` to `a`
        have h3' : revParam β 0 ∉ revParam γ₁ '' Icc 0 1 := by
          rw [revParam_zero, hβ1, revParam_image]
          intro h
          rcases hγ₁img h with h' | h'
          · exact hbR h'
          · simp at h'; exact hab h'.symm
        have h4' : revParam β 1 ∈ revParam γ₁ '' Icc 0 1 := by
          rw [revParam_one, revParam_image, ← hπ1, ← hγ₁1]
          exact ⟨1, ⟨zero_le_one, le_refl 1⟩, rfl⟩
        obtain ⟨γ₂, hγ₂, hγ₂0, hγ₂1, hγ₂sub⟩ := exists_arc_cut hβarc.rev hγ₁.rev h3' h4'
        have hg0 : revParam γ₂ 0 = a := by
          rw [revParam_zero, hγ₂1, revParam_one, hγ₁0']
        have hg1 : revParam γ₂ 1 = b := by rw [revParam_one, hγ₂0, revParam_zero, hβ1]
        refine ⟨revParam γ₂, hγ₂.rev, hg0, hg1, ?_⟩
        refine (hγ₂.rev).image_Ioo_subset_of_image_subset hg0 hg1 ?_
        rw [revParam_image]
        refine hγ₂sub.trans ?_
        rw [revParam_image, revParam_image]
        rintro x (hx | hx)
        · rcases hβimg hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])
        · rcases hγ₁img hx with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])

/-- Three points accessible from an open, path-connected set `R` can be joined to a common
point `c` of `R` by three arcs whose relative interiors lie in `R` and which meet only at
`c`.

This is the "plane tree" construction of footnote 10 of
Klein–Langetepe–Nilforoushan (2009), used in the proof of Lemma 9:

> This can be achieved as follows.  First, we choose `α_{1,j}`.  Then we trace `α_{2,j}` from
> `v₂` to `a_j`, and cut it at the first point of `α_{1,j}` it meets.  Finally we trace
> `α_{3,j}` from `v₃` to `a_j`, and cut it at the first point of the partial tree already
> constructed.

The common point `c` is the branch point of the resulting plane tree (the median of its
three leaves), so that the three arcs from the leaves to `c` meet exactly in `c`.  The
proof given here builds the tree as the paper does: an arc `A` joins `v 0` to `v 1`
through `R` (by `exists_arc_of_accessible`), a second arc `B` joins `v 2` to the interior
point `A (1/2)` of the first one, and `B` is cut at the first point `c` where it meets
`A`; the three branches of the star are then the two halves of `A` and the initial piece
of `B`. -/
theorem exists_star_of_accessible {R : Set Plane} (hopen : IsOpen R)
    (hconn : ∀ x ∈ R, ∀ y ∈ R, JoinedIn R x y) {v : Fin 3 → Plane}
    (hv : Function.Injective v) (hvR : ∀ i, v i ∉ R) (hacc : ∀ i, AccessibleFrom R (v i)) :
    ∃ c ∈ R, ∃ α : Fin 3 → (ℝ → Plane),
      (∀ i, IsArc (α i) ∧ α i 0 = v i ∧ α i 1 = c ∧ α i '' Ioo 0 1 ⊆ R) ∧
      ∀ i i', i ≠ i' → α i '' Icc 0 1 ∩ α i' '' Icc 0 1 = {c} := by
  have hne01 : v 0 ≠ v 1 := fun h => absurd (hv h) (by decide)
  have hne20 : v 2 ≠ v 0 := fun h => absurd (hv h) (by decide)
  have hne21 : v 2 ≠ v 1 := fun h => absurd (hv h) (by decide)
  -- the trunk of the tree: an arc from `v 0` to `v 1` through `R`
  obtain ⟨A, hA, hA0, hA1, hAIoo⟩ := exists_arc_of_accessible hopen hconn hne01 (hacc 0) (hacc 1)
  have hm : A (1/2) ∈ R := hAIoo ⟨1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hv2m : v 2 ≠ A (1/2) := fun h => hvR 2 (h ▸ hm)
  -- the third branch: an arc from `v 2` to an interior point of the trunk
  obtain ⟨B, hB, hB0, hB1, hBIoo⟩ :=
    exists_arc_of_accessible hopen hconn hv2m (hacc 2) (accessible_of_mem_open hopen hm)
  have hAimg : A '' Icc 0 1 ⊆ R ∪ {v 0, v 1} := by
    rw [image_Icc_eq_union_endpoints, hA0, hA1]
    exact union_subset_union hAIoo (subset_refl _)
  have hAclosed : IsClosed (A '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hA.cont).isClosed
  have hstart : B 0 ∉ A '' Icc 0 1 := by
    rw [hB0]
    intro h
    rcases hAimg h with h' | h'
    · exact hvR 2 h'
    · simp only [mem_insert_iff, mem_singleton_iff] at h'
      rcases h' with h' | h'
      · exact hne20 h'
      · exact hne21 h'
  have hend : B 1 ∈ A '' Icc 0 1 := by
    rw [hB1]; exact ⟨1/2, ⟨by norm_num, by norm_num⟩, rfl⟩
  -- cut the third branch at the first point where it meets the trunk
  obtain ⟨t, ht, htA, hfirst⟩ := exists_first_hit hB.cont hAclosed hstart hend
  have hzR : B t ∈ R := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hB1]; exact hm
    · exact hBIoo ⟨t, ⟨ht.1, h⟩, rfl⟩
  obtain ⟨u, hu, huz⟩ : ∃ u ∈ Icc (0 : ℝ) 1, A u = B t := htA
  have hu0 : 0 < u := by
    rcases eq_or_lt_of_le hu.1 with h | h
    · exfalso
      rw [← h, hA0] at huz
      exact hvR 0 (huz ▸ hzR)
    · exact h
  have hu1 : u < 1 := by
    rcases eq_or_lt_of_le hu.2 with h | h
    · exfalso
      rw [h, hA1] at huz
      exact hvR 1 (huz ▸ hzR)
    · exact h
  -- the three branches of the star, all ending at the branch point `B t`
  set a0 := subarcParam A 0 u with ha0def
  set a1 := revParam (subarcParam A u 1) with ha1def
  set a2 := subarcParam B 0 t with ha2def
  have harc0 : IsArc a0 := hA.subarc (le_refl 0) hu0 hu.2
  have harc1 : IsArc a1 := (hA.subarc hu.1 hu1 (le_refl 1)).rev
  have harc2 : IsArc a2 := hB.subarc (le_refl 0) ht.1 ht.2
  have himg0 : a0 '' Icc 0 1 = A '' Icc 0 u := subarcParam_image hu0.le
  have himg1 : a1 '' Icc 0 1 = A '' Icc u 1 := by
    rw [ha1def, revParam_image, subarcParam_image hu1.le]
  have himg2 : a2 '' Icc 0 1 = B '' Icc 0 t := subarcParam_image ht.1.le
  have hval00 : a0 0 = v 0 := by rw [ha0def, subarcParam_zero, hA0]
  have hval01 : a0 1 = B t := by rw [ha0def, subarcParam_one, huz]
  have hval10 : a1 0 = v 1 := by rw [ha1def, revParam_zero, subarcParam_one, hA1]
  have hval11 : a1 1 = B t := by rw [ha1def, revParam_one, subarcParam_zero, huz]
  have hval20 : a2 0 = v 2 := by rw [ha2def, subarcParam_zero, hB0]
  have hval21 : a2 1 = B t := by rw [ha2def, subarcParam_one]
  have hint0 : a0 '' Ioo 0 1 ⊆ R := by
    rw [ha0def, subarcParam_image_Ioo hu0]
    exact (Set.image_mono (Ioo_subset_Ioo (le_refl 0) hu.2)).trans hAIoo
  have hint1 : a1 '' Ioo 0 1 ⊆ R := by
    rw [ha1def, revParam_image_Ioo, subarcParam_image_Ioo hu1]
    exact (Set.image_mono (Ioo_subset_Ioo hu.1 (le_refl 1))).trans hAIoo
  have hint2 : a2 '' Ioo 0 1 ⊆ R := by
    rw [ha2def, subarcParam_image_Ioo ht.1]
    exact (Set.image_mono (Ioo_subset_Ioo (le_refl 0) ht.2)).trans hBIoo
  -- the two halves of the trunk meet only at the branch point
  have hI01 : a0 '' Icc 0 1 ∩ a1 '' Icc 0 1 = {B t} := by
    rw [himg0, himg1]
    apply Subset.antisymm
    · rintro x ⟨⟨s, hs, rfl⟩, ⟨s', hs', hss'⟩⟩
      have hss : s = s' :=
        hA.inj ⟨hs.1, hs.2.trans hu.2⟩ ⟨hu.1.trans hs'.1, hs'.2⟩ hss'.symm
      have hsu : s = u := le_antisymm hs.2 (hss ▸ hs'.1)
      rw [mem_singleton_iff, hsu, huz]
    · rintro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨u, ⟨hu.1, le_refl u⟩, huz⟩, ⟨u, ⟨le_refl u, hu.2⟩, huz⟩⟩
  -- the third branch meets the trunk only at the branch point
  have hcut : ∀ x, x ∈ B '' Icc 0 t → x ∈ A '' Icc 0 1 → x = B t := by
    rintro x ⟨s, hs, rfl⟩ hxA
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]
    · exact absurd hxA (hfirst s ⟨hs.1, h⟩)
  have hI02 : a0 '' Icc 0 1 ∩ a2 '' Icc 0 1 = {B t} := by
    rw [himg0, himg2]
    apply Subset.antisymm
    · rintro x ⟨hxA, hxB⟩
      exact mem_singleton_iff.2
        (hcut x hxB (Set.image_mono (Icc_subset_Icc (le_refl 0) hu.2) hxA))
    · rintro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨u, ⟨hu.1, le_refl u⟩, huz⟩, ⟨t, ⟨ht.1.le, le_refl t⟩, rfl⟩⟩
  have hI12 : a1 '' Icc 0 1 ∩ a2 '' Icc 0 1 = {B t} := by
    rw [himg1, himg2]
    apply Subset.antisymm
    · rintro x ⟨hxA, hxB⟩
      exact mem_singleton_iff.2
        (hcut x hxB (Set.image_mono (Icc_subset_Icc hu.1 (le_refl 1)) hxA))
    · rintro x hx
      rw [mem_singleton_iff] at hx
      subst hx
      exact ⟨⟨u, ⟨le_refl u, hu.2⟩, huz⟩, ⟨t, ⟨ht.1.le, le_refl t⟩, rfl⟩⟩
  refine ⟨B t, hzR, ![a0, a1, a2], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨harc0, hval00, hval01, hint0⟩
    · exact ⟨harc1, hval10, hval11, hint1⟩
    · exact ⟨harc2, hval20, hval21, hint2⟩
  · intro i i' hii
    fin_cases i <;> fin_cases i' <;>
      first
        | exact absurd rfl hii
        | exact hI01
        | exact hI02
        | exact hI12
        | (rw [Set.inter_comm]; first | exact hI01 | exact hI02 | exact hI12)

/-- Two arcs with the same pair of (distinct) endpoints whose relative interiors are
disjoint form a closed Jordan curve.  (The hypothesis that the two endpoints are distinct,
which is satisfied in the application, turns out not to be needed.)

This is used in the proof of Lemma 6 of Klein–Langetepe–Nilforoushan (2009): "Together,
arcs `π ⊆ VR(p,S)` and `ρ ⊆ VR(r,S)` form a closed Jordan curve". -/
theorem isClosedJordanCurve_of_arcs {π ρ : ℝ → Plane} (hπ : IsArc π) (hρ : IsArc ρ)
    (h0 : π 0 = ρ 0) (h1 : π 1 = ρ 1)
    (hdisj : Disjoint (π '' Ioo 0 1) (ρ '' Ioo 0 1)) :
    IsClosedJordanCurve (π '' Icc 0 1 ∪ ρ '' Icc 0 1) := by
  classical
  set γ : ℝ → Plane := Set.piecewise (Iic (1/2 : ℝ)) (fun x => π (2 * x))
    (fun x => ρ (2 - 2 * x)) with hγdef
  have hmem : ∀ x : ℝ, x ≤ 1/2 → γ x = π (2 * x) := by
    intro x hx
    rw [hγdef, Set.piecewise_eq_of_mem _ _ _ (by simpa using hx)]
  have hnotmem : ∀ x : ℝ, ¬ x ≤ 1/2 → γ x = ρ (2 - 2 * x) := by
    intro x hx
    rw [hγdef, Set.piecewise_eq_of_notMem _ _ _ (by simpa using hx)]
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · -- continuity, by gluing the two halves at `1/2`
    refine ContinuousOn.piecewise ?_ ?_ ?_
    · intro a ha
      have ha' : a = 1/2 := by simpa [frontier_Iic] using ha.2
      subst ha'
      norm_num [h1]
    · refine hπ.cont.comp (by fun_prop) ?_
      rintro x ⟨hx, hx'⟩
      rw [closure_Iic] at hx'
      simp only [mem_Icc] at hx ⊢
      simp only [mem_Iic] at hx'
      constructor <;> linarith [hx.1, hx.2]
    · refine hρ.cont.comp (by fun_prop) ?_
      rintro x ⟨hx, hx'⟩
      rw [compl_Iic, closure_Ioi] at hx'
      simp only [mem_Icc] at hx ⊢
      simp only [mem_Ici] at hx'
      constructor <;> linarith [hx.1, hx.2]
  · -- injectivity on `[0,1)`
    intro x hx y hy hxy
    rcases le_or_gt x (1/2) with hx2 | hx2 <;> rcases le_or_gt y (1/2) with hy2 | hy2
    · rw [hmem x hx2, hmem y hy2] at hxy
      have := hπ.inj ⟨by linarith [hx.1], by linarith [hx2]⟩
        ⟨by linarith [hy.1], by linarith [hy2]⟩ hxy
      linarith
    · rw [hmem x hx2, hnotmem y (not_le.2 hy2)] at hxy
      exfalso
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · -- `x = 0`, so `π 0 = ρ 0`, forcing `y = 1`, impossible
        rw [← hx0] at hxy
        have : (0 : ℝ) = 2 - 2 * y := by
          refine hρ.inj ⟨le_refl 0, by norm_num⟩
            ⟨by linarith [hy.2], by linarith [hy2]⟩ ?_
          rw [← h0]
          simpa using hxy
        linarith [hy.2]
      · rcases eq_or_lt_of_le (show 2 * x ≤ 1 by linarith) with hx1 | hx1
        · -- `x = 1/2`, so `π 1 = ρ 1`, forcing `y = 1/2`, impossible
          have : (1 : ℝ) = 2 - 2 * y := by
            refine hρ.inj ⟨by norm_num, le_refl 1⟩
              ⟨by linarith [hy.2], by linarith [hy2]⟩ ?_
            rw [← h1, ← hx1]
            exact hxy
          linarith
        · -- the relative interiors of the two arcs are disjoint
          exact (Set.disjoint_left.1 hdisj) ⟨2 * x, ⟨by linarith, hx1⟩, rfl⟩
            ⟨2 - 2 * y, ⟨by linarith [hy.2], by linarith⟩, hxy.symm⟩
    · rw [hnotmem x (not_le.2 hx2), hmem y hy2] at hxy
      exfalso
      rcases eq_or_lt_of_le hy.1 with hy0 | hy0
      · rw [← hy0] at hxy
        have : (0 : ℝ) = 2 - 2 * x := by
          refine hρ.inj ⟨le_refl 0, by norm_num⟩
            ⟨by linarith [hx.2], by linarith [hx2]⟩ ?_
          rw [← h0]
          simpa using hxy.symm
        linarith [hx.2]
      · rcases eq_or_lt_of_le (show 2 * y ≤ 1 by linarith) with hy1 | hy1
        · have : (1 : ℝ) = 2 - 2 * x := by
            refine hρ.inj ⟨by norm_num, le_refl 1⟩
              ⟨by linarith [hx.2], by linarith [hx2]⟩ ?_
            rw [← h1, ← hy1]
            exact hxy.symm
          linarith
        · exact (Set.disjoint_left.1 hdisj) ⟨2 * y, ⟨by linarith, hy1⟩, rfl⟩
            ⟨2 - 2 * x, ⟨by linarith [hx.2], by linarith⟩, hxy⟩
    · rw [hnotmem x (not_le.2 hx2), hnotmem y (not_le.2 hy2)] at hxy
      have := hρ.inj ⟨by linarith [hx.2], by linarith [hx2]⟩
        ⟨by linarith [hy.2], by linarith [hy2]⟩ hxy
      linarith
  · -- the curve is closed
    rw [hmem 0 (by norm_num), hnotmem 1 (by norm_num)]
    simp [h0]
  · -- the image is the union of the two arcs
    apply Subset.antisymm
    · rintro x ⟨c, hc, rfl⟩
      rcases le_or_gt c (1/2) with hc2 | hc2
      · exact Or.inl ⟨2 * c, ⟨by linarith [hc.1], by linarith⟩, (hmem c hc2).symm⟩
      · exact Or.inr ⟨2 - 2 * c, ⟨by linarith [hc.2], by linarith⟩,
          (hnotmem c (not_le.2 hc2)).symm⟩
    · rintro x (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact ⟨c / 2, ⟨by linarith [hc.1], by linarith [hc.2]⟩, by
          rw [hmem (c/2) (by linarith [hc.2])]; ring_nf⟩
      · rcases eq_or_lt_of_le hc.2 with hc1 | hc1
        · refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
          rw [hmem (1/2) (le_refl _)]
          norm_num
          rw [h1, hc1]
        · refine ⟨1 - c / 2, ⟨by linarith [hc.2], by linarith [hc.1]⟩, ?_⟩
          rw [hnotmem (1 - c/2) (by intro h; linarith)]
          ring_nf

end AVD
