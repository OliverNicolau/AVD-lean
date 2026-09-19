import AbstractVoronoi.Paper.Lemma6

/-!
# Local branches of two bisecting curves

API on the two local branches of a bisecting curve at a common point of two curves, used
in the proofs of Lemma 7 and Lemma 8 of R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract
Voronoi diagrams revisited*, Computational Geometry 42 (2009) 885–902.
-/

noncomputable section

open Set Topology

namespace AVD

namespace CurveSystem

variable {ι : Type*} [DecidableEq ι] {S : Finset ι} {C : CurveSystem S}

/-- A consequence of **Lemma 6** of Klein–Langetepe–Nilforoushan (2009), stated in the
discussion preceding Lemma 7: the two branches of the bisecting curve `J(p,q)` at a point
`f 0` each stay in the closure of one of the two half-planes defined by `J(p,r)`.  (The
paper phrases this for `J(p,r)` and `J(p,q)`; both instances are obtained from this lemma by
exchanging `q` and `r`.) -/
theorem branch_dichotomy (hadm : C.Admissible) {p q r : ι} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {f : ℝ → Plane} (hf : IsProperLineParam f (C.J p q)) :
    (BranchBefore f (closure (C.D p r)) ∨ BranchBefore f (closure (C.D r p))) ∧
      (BranchAfter f (closure (C.D p r)) ∨ BranchAfter f (closure (C.D r p))) := by
  -- a point outside the closure of one half-plane lies in the other one
  have hout1 : ∀ x : Plane, x ∉ closure (C.D p r) → x ∈ C.D r p := by
    intro x hx
    rw [closure_D_eq hadm hp hr hpr] at hx
    have h1 : x ∉ C.D p r := fun h => hx (Or.inl h)
    have h2 : x ∉ C.J p r := fun h => hx (Or.inr h)
    have : x ∈ (C.J p r)ᶜ := h2
    rw [C.compl_J p hp r hr hpr] at this
    rcases this with h | h
    · exact absurd h h1
    · exact h
  have hout2 : ∀ x : Plane, x ∉ closure (C.D r p) → x ∈ C.D p r := by
    intro x hx
    rw [closure_D_eq hadm hr hp (Ne.symm hpr)] at hx
    have h1 : x ∉ C.D r p := fun h => hx (Or.inl h)
    have h2 : x ∉ C.J r p := fun h => hx (Or.inr h)
    have hx' : x ∈ (C.J r p)ᶜ := h2
    rw [C.compl_J r hr p hp (Ne.symm hpr)] at hx'
    rcases hx' with h | h
    · exact absurd h h1
    · exact h
  constructor
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hA : ∀ δ : ℝ, 0 < δ → ∃ a ∈ Ioo (-δ) (0 : ℝ), f a ∈ C.D r p := by
      intro δ hδ
      by_contra hcon2
      push Not at hcon2
      refine h1 ⟨δ, hδ, ?_⟩
      rintro x ⟨c, hc, rfl⟩
      by_contra hx
      exact hcon2 c hc (hout1 _ hx)
    have hB : ∀ δ : ℝ, 0 < δ → ∃ b ∈ Ioo (-δ) (0 : ℝ), f b ∈ C.D p r := by
      intro δ hδ
      by_contra hcon2
      push Not at hcon2
      refine h2 ⟨δ, hδ, ?_⟩
      rintro x ⟨c, hc, rfl⟩
      by_contra hx
      exact hcon2 c hc (hout2 _ hx)
    obtain ⟨a₁, ha₁, hfa₁⟩ := hA 1 one_pos
    obtain ⟨b₁, hb₁, hfb₁⟩ := hB (-a₁) (by linarith [ha₁.2])
    obtain ⟨a₂, ha₂, hfa₂⟩ := hA (-b₁) (by linarith [hb₁.2])
    obtain ⟨b₂, hb₂, hfb₂⟩ := hB (-a₂) (by linarith [ha₂.2])
    exact lemma6 hadm hp hr hq hpr (Ne.symm hqr) hpq hf
      (by linarith [hb₁.1]) (by linarith [ha₂.1]) (by linarith [hb₂.1])
      (Or.inl ⟨hfa₁, hfb₁, hfa₂, hfb₂⟩)
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hA : ∀ δ : ℝ, 0 < δ → ∃ a ∈ Ioo (0 : ℝ) δ, f a ∈ C.D r p := by
      intro δ hδ
      by_contra hcon2
      push Not at hcon2
      refine h1 ⟨δ, hδ, ?_⟩
      rintro x ⟨c, hc, rfl⟩
      by_contra hx
      exact hcon2 c hc (hout1 _ hx)
    have hB : ∀ δ : ℝ, 0 < δ → ∃ b ∈ Ioo (0 : ℝ) δ, f b ∈ C.D p r := by
      intro δ hδ
      by_contra hcon2
      push Not at hcon2
      refine h2 ⟨δ, hδ, ?_⟩
      rintro x ⟨c, hc, rfl⟩
      by_contra hx
      exact hcon2 c hc (hout2 _ hx)
    obtain ⟨a₁, ha₁, hfa₁⟩ := hA 1 one_pos
    obtain ⟨b₁, hb₁, hfb₁⟩ := hB a₁ ha₁.1
    obtain ⟨a₂, ha₂, hfa₂⟩ := hA b₁ hb₁.1
    obtain ⟨b₂, hb₂, hfb₂⟩ := hB a₂ ha₂.1
    exact lemma6 hadm hp hr hq hpr (Ne.symm hqr) hpq hf
      (by linarith [hb₂.2]) (by linarith [ha₂.2]) (by linarith [hb₁.2])
      (Or.inr ⟨hfb₂, hfa₂, hfb₁, hfa₁⟩)

/-- The key step of **Lemma 7** of Klein–Langetepe–Nilforoushan (2009).

If both branches of `J(p,r)` at the common point `w` stay in the closure of the half-plane
`D(b,a)` of the curve `J(a,b)`, then `J(a,b)` cannot cross `J(p,r)` at `w`: there cannot be
points of `J(a,b)` arbitrarily close to `w` on both sides of `J(p,r)`.

The proof is the one of the paper: inside a neighbourhood `U` of `w` in which the two
domains of `J(a,b)` are connected (Theorem 4), two such points `z ∈ D(p,r)` and
`z' ∈ D(r,p)` can be joined by an arc running in `U ∩ D(a,b)`; that arc must meet `J(p,r)`,
but near `w` the curve `J(p,r)` stays in the closure of `D(b,a)`, which is disjoint from
`D(a,b)`. -/
theorem not_crossing_aux (hadm : C.Admissible) {p r a b : ι} (hp : p ∈ S) (hr : r ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (hpr : p ≠ r) {w : Plane} {g : ℝ → Plane}
    (hg : IsProperLineParamAt g (C.J p r) w) (hw : w ∈ C.J a b)
    (hGb : BranchBefore g (closure (C.D b a))) (hGa : BranchAfter g (closure (C.D b a)))
    (hz : ∀ V ∈ 𝓝 w, ∃ z ∈ V, z ∈ C.J a b ∧ z ∈ C.D p r)
    (hz' : ∀ V ∈ 𝓝 w, ∃ z' ∈ V, z' ∈ C.J a b ∧ z' ∈ C.D r p) : False := by
  obtain ⟨⟨hgcont, hginj, hgrange, hgproper⟩, hg0⟩ := hg
  -- a piece of `J(p,r)` around `w` stays in the closure of `D(b,a)`
  obtain ⟨δ₁, hδ₁, hsub₁⟩ := hGb
  obtain ⟨δ₂, hδ₂, hsub₂⟩ := hGa
  have hwcl : w ∈ closure (C.D b a) := by
    refine frontier_subset_closure ?_
    rw [frontier_D_eq_J hadm hb ha (Ne.symm hab), C.J_symm hb ha (Ne.symm hab)]
    exact hw
  have hgδ : g '' Ioo (-min δ₁ δ₂) (min δ₁ δ₂) ⊆ closure (C.D b a) := by
    rintro x ⟨c, hc, rfl⟩
    rcases lt_trichotomy c 0 with h | h | h
    · exact hsub₁ ⟨c, ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δ₁ δ₂)) hc.1, h⟩, rfl⟩
    · rw [h, hg0]; exact hwcl
    · exact hsub₂ ⟨c, ⟨h, lt_of_lt_of_le hc.2 (min_le_right δ₁ δ₂)⟩, rfl⟩
  obtain ⟨W, hWopen, hwW, hWsub⟩ :=
    IsProperLineParam.exists_nbhd ⟨hgcont, hginj, hgrange, hgproper⟩ (lt_min hδ₁ hδ₂)
  rw [hg0] at hwW
  have hWcl : ∀ x ∈ C.J p r, x ∈ W → x ∈ closure (C.D b a) := by
    intro x hx hxW
    exact hgδ (hWsub ⟨hx, hxW⟩)
  -- a neighbourhood `U` of `w` in which `D(a,b)` is connected
  obtain ⟨-, hacc⟩ := exists_theorem4_data hadm ha hb hab
  obtain ⟨U, hUnhds, hUW, hUopen, hUconn, -⟩ := hacc w hw W (hWopen.mem_nhds hwW)
  obtain ⟨z, hzU, hzJ, hzD⟩ := hz U hUnhds
  obtain ⟨z', hz'U, hz'J, hz'D⟩ := hz' U hUnhds
  -- both points are accessible from the connected open set `U ∩ D(a,b)`
  have hzacc : AccessibleFrom (U ∩ C.D a b) z :=
    accessibleFrom_of_mem_J hadm ha hb hab hzJ (hUopen.mem_nhds hzU)
  have hz'acc : AccessibleFrom (U ∩ C.D a b) z' :=
    accessibleFrom_of_mem_J hadm ha hb hab hz'J (hUopen.mem_nhds hz'U)
  have hRopen : IsOpen (U ∩ C.D a b) := hUopen.inter (C.D_isOpen a ha b hb hab)
  have hRpath : IsPathConnected (U ∩ C.D a b) :=
    (hRopen.isConnected_iff_isPathConnected).1 hUconn
  have hzz' : z ≠ z' := by
    intro h
    exact (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) hzD (h ▸ hz'D)
  obtain ⟨σ, hσarc, hσ0, hσ1, hσint⟩ :=
    exists_arc_of_accessible hRopen (fun x hx y hy => hRpath.joinedIn x hx y hy) hzz'
      hzacc hz'acc
  -- the arc must cross `J(p,r)`
  have hconn : IsPreconnected (σ '' Icc 0 1) := isPreconnected_Icc.image σ hσarc.cont
  have hmeet : ∃ y ∈ σ '' Icc 0 1, y ∈ C.J p r := by
    by_contra hcon
    push Not at hcon
    have hsub : σ '' Icc 0 1 ⊆ C.D p r ∪ C.D r p := by
      intro y hy
      have : y ∈ (C.J p r)ᶜ := hcon y hy
      rw [C.compl_J p hp r hr hpr] at this
      exact this
    rcases hconn.subset_or_subset (C.D_isOpen p hp r hr hpr)
      (C.D_isOpen r hr p hp (Ne.symm hpr)) (C.D_disjoint p hp r hr hpr) hsub with h | h
    · refine (Set.disjoint_left.1 (C.D_disjoint p hp r hr hpr)) ?_ hz'D
      have := h ⟨1, ⟨by norm_num, le_refl 1⟩, rfl⟩
      rwa [hσ1] at this
    · refine (Set.disjoint_left.1 (C.D_disjoint r hr p hp (Ne.symm hpr))) ?_ hzD
      have := h ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩
      rwa [hσ0] at this
  obtain ⟨y, ⟨c, hc, rfl⟩, hyJ⟩ := hmeet
  -- the crossing point is an interior point of the arc, hence lies in `U ∩ D(a,b)`
  have hcint : c ∈ Ioo (0 : ℝ) 1 := by
    rcases eq_or_lt_of_le hc.1 with h | h
    · exfalso
      rw [← h, hσ0] at hyJ
      exact (notMem_D_of_mem_J hp hr hpr hyJ).1 hzD
    · rcases eq_or_lt_of_le hc.2 with h' | h'
      · exfalso
        rw [h', hσ1] at hyJ
        exact (notMem_D_of_mem_J hp hr hpr hyJ).2 hz'D
      · exact ⟨h, h'⟩
  have hyR : σ c ∈ U ∩ C.D a b := hσint ⟨c, hcint, rfl⟩
  have hycl : σ c ∈ closure (C.D b a) := hWcl _ hyJ (hUW hyR.1)
  rw [closure_D_eq hadm hb ha (Ne.symm hab)] at hycl
  rcases hycl with h | h
  · exact (Set.disjoint_left.1 (C.D_disjoint b hb a ha (Ne.symm hab))) h hyR.2
  · rw [C.J_symm hb ha (Ne.symm hab)] at h
    exact (notMem_D_of_mem_J ha hb hab h).1 hyR.2

end CurveSystem

end AVD
