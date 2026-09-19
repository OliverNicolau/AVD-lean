import AbstractVoronoi.Jordan.ArcSurgery

/-!
# Arcs ending at a limit point of a nested family of domains

This file contains a purely topological construction which is used to prove the
*accessibility* statements of Theorem 4 of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

The situation is the following.  A point `z` of the plane is given, together with a
decreasing sequence `W 0 ⊇ W 1 ⊇ ⋯` of non-empty open connected sets shrinking to `z`
(`W n ⊆ ball z εₙ` with `εₙ → 0`), none of which contains `z`.  Then `z` is *accessible*
from `W 0`: there is an arc which starts at any prescribed point of `W 0`, runs inside
`W 0`, and ends at `z` (`AVD.exists_arc_to_limit`).

The construction is the classical one.  One builds an increasing sequence of arcs, each
obtained from the previous one by cutting it at the last point where it meets a new arc
running deeper into the family, and by appending the remaining piece of the latter.  The
crucial point, which makes the sequence of arcs converge, is that the new arc is chosen
inside a member `W k` of the family that is disjoint from the *stable* part of the current
arc, so that the cutting only affects the last piece.  The limit is then an arc, because
any two of its parameters lie in an initial part where it agrees with one of the
approximating arcs.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-! ## The approximating arcs -/

/-- An *approximating arc* for the construction of `AVD.exists_arc_to_limit`: an arc
`param` parametrized by `[0, len]`, running inside `W 0`, whose endpoint lies in the deep
member `W idx` of the family, and whose *stable* initial part `param '' [0, stab]` is
disjoint from `W idx`.  The last condition is what guarantees that the next step of the
construction does not modify the stable part. -/
structure ArcApprox (W : ℕ → Set Plane) where
  /-- the parametrization of the approximating arc -/
  param : ℝ → Plane
  /-- the length of the parameter interval -/
  len : ℝ
  /-- the end of the part of the arc which is already final -/
  stab : ℝ
  /-- the index of the member of the family containing the endpoint -/
  idx : ℕ
  stab_nonneg : 0 ≤ stab
  stab_lt : stab < len
  cont : ContinuousOn param (Icc 0 len)
  inj : InjOn param (Icc 0 len)
  sub : param '' Icc 0 len ⊆ W 0
  endpt : param len ∈ W idx
  disj : Disjoint (W idx) (param '' Icc 0 stab)

namespace ArcApprox

variable {W : ℕ → Set Plane} {z : Plane}

/-- The relation between two successive approximating arcs of the construction. -/
def Link (st st' : ArcApprox W) : Prop :=
  st.idx < st'.idx ∧ st.stab < st'.stab ∧ st'.stab ≤ st.len ∧
    st'.len - st'.stab ≤ (st.len - st.stab) / 2 ∧
    (∀ t ≤ st'.stab, st'.param t = st.param t) ∧
    st'.param '' Icc st'.stab st'.len ⊆ W st.idx

end ArcApprox

section Construction

variable {W : ℕ → Set Plane} {z : Plane}

/-- **The step of the construction.**  Given an approximating arc, one can find a next one:
a new arc is run from the endpoint of the given one into a deeper member of the family, the
given arc is cut at the last point where the new one meets it, and the remaining piece of
the new arc is appended. -/
theorem exists_link (hWopen : ∀ n, IsOpen (W n)) (hWconn : ∀ n, IsPreconnected (W n))
    (hWne : ∀ n, (W n).Nonempty) (hWanti : Antitone W)
    (hWsmall : ∀ ε > 0, ∃ n, W n ⊆ ball z ε) (hz : z ∉ W 0) (st : ArcApprox W) :
    ∃ st' : ArcApprox W, st.Link st' := by
  classical
  obtain ⟨β, L, s, m, hs0, hsL, hcont, hinj, hsub, hend, hdisj⟩ := st
  simp only [ArcApprox.Link]
  -- the image of the given arc
  have hKcompact : IsCompact (β '' Icc 0 L) := isCompact_Icc.image_of_continuousOn hcont
  have hKclosed : IsClosed (β '' Icc 0 L) := hKcompact.isClosed
  have hzK : z ∉ β '' Icc 0 L := fun h => hz (hsub h)
  have hKne : (β '' Icc 0 L).Nonempty := ⟨β 0, ⟨0, ⟨le_refl 0, by linarith⟩, rfl⟩⟩
  have hd : 0 < infDist z (β '' Icc 0 L) := by
    rw [← hKclosed.notMem_iff_infDist_pos hKne]
    exact hzK
  -- a member of the family missing the whole arc
  obtain ⟨n₀, hn₀⟩ := hWsmall _ hd
  set m' := max (m + 1) n₀ with hm'def
  have hmm' : m < m' := lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_left _ _)
  have hWm'sub : W m' ⊆ ball z (infDist z (β '' Icc 0 L)) :=
    (hWanti (le_max_right (m + 1) n₀)).trans hn₀
  have hdisjK : Disjoint (W m') (β '' Icc 0 L) := by
    rw [Set.disjoint_left]
    intro x hx hxK
    have h1 : dist x z < infDist z (β '' Icc 0 L) := by
      have hb := hWm'sub hx
      rwa [mem_ball] at hb
    have h2 : infDist z (β '' Icc 0 L) ≤ dist z x := infDist_le_dist_of_mem hxK
    rw [dist_comm] at h1
    linarith
  obtain ⟨v, hv⟩ := hWne m'
  have hvK : v ∉ β '' Icc 0 L := fun h => (Set.disjoint_left.1 hdisjK) hv h
  have hendK : β L ∈ β '' Icc 0 L := ⟨L, ⟨by linarith, le_refl L⟩, rfl⟩
  have hne : β L ≠ v := fun h => hvK (h ▸ hendK)
  have hvWm : v ∈ W m := hWanti (le_of_lt hmm') hv
  -- the connecting arc, inside `W m`
  obtain ⟨A, hA, hA0, hA1, hAsub⟩ := exists_arc_in_open (hWopen m) (hWconn m) hend hvWm hne
  -- the last point where it meets the given arc
  have hTclosed : IsClosed (Icc (0 : ℝ) 1 ∩ A ⁻¹' (β '' Icc 0 L)) :=
    hA.cont.preimage_isClosed_of_isClosed isClosed_Icc hKclosed
  have hT0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∩ A ⁻¹' (β '' Icc 0 L) :=
    ⟨⟨le_refl 0, zero_le_one⟩, by simp only [mem_preimage, hA0]; exact hendK⟩
  have hTbdd : BddAbove (Icc (0 : ℝ) 1 ∩ A ⁻¹' (β '' Icc 0 L)) := ⟨1, fun t ht => ht.1.2⟩
  set τ := sSup (Icc (0 : ℝ) 1 ∩ A ⁻¹' (β '' Icc 0 L)) with hτdef
  have hτT : τ ∈ Icc (0 : ℝ) 1 ∩ A ⁻¹' (β '' Icc 0 L) :=
    hTclosed.csSup_mem ⟨0, hT0⟩ hTbdd
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := hτT.1
  have hτ1 : τ < 1 := by
    rcases eq_or_lt_of_le hτ01.2 with h | h
    · exfalso; apply hvK; rw [← hA1, ← h]; exact hτT.2
    · exact h
  have hafter : ∀ t, τ < t → t ≤ 1 → A t ∉ β '' Icc 0 L := by
    intro t ht ht1 hmem
    exact absurd (le_csSup hTbdd ⟨⟨le_trans hτ01.1 ht.le, ht1⟩, hmem⟩) (not_le.2 ht)
  obtain ⟨σ, hσ, hσy⟩ : ∃ σ ∈ Icc (0 : ℝ) L, β σ = A τ := hτT.2
  have hAτ : A τ ∈ W m := hAsub ⟨τ, hτ01, rfl⟩
  have hsσ : s < σ := by
    by_contra hcon
    exact (Set.disjoint_left.1 hdisj) hAτ ⟨σ, ⟨hσ.1, not_lt.1 hcon⟩, hσy⟩
  -- the new parametrization
  set c := (L - s) / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  set L' := σ + c with hL'def
  have hσL' : σ < L' := by rw [hL'def]; linarith
  set k : ℝ := (1 - τ) / c with hkdef
  have hk0 : 0 < k := div_pos (by linarith) hc0
  have hkc : k * c = 1 - τ := by
    rw [hkdef]
    field_simp
  set ψ : ℝ → ℝ := fun t => τ + k * (t - σ) with hψdef
  have hψcont : Continuous ψ := by
    rw [hψdef]; fun_prop
  have hψσ : ψ σ = τ := by simp [hψdef]
  have hψL' : ψ L' = 1 := by
    rw [hψdef, hL'def]
    simp only [add_sub_cancel_left]
    linarith [hkc]
  have hψmono : StrictMonoOn ψ (Icc σ L') := by
    intro a _ b _ hab
    rw [hψdef]
    have : k * (a - σ) < k * (b - σ) := by nlinarith
    linarith
  have hψmaps : ∀ t ∈ Icc σ L', ψ t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    have h1 : 0 ≤ k * (t - σ) := mul_nonneg hk0.le (by linarith [ht.1])
    have h2 : k * (t - σ) ≤ 1 - τ := by
      have : t - σ ≤ c := by
        have := ht.2
        rw [hL'def] at this
        linarith
      nlinarith
    constructor
    · rw [hψdef]; simp only; linarith [hτ01.1]
    · rw [hψdef]; simp only; linarith
  have hψgt : ∀ t, σ < t → τ < ψ t := by
    intro t ht
    rw [hψdef]
    have h1 : 0 < k * (t - σ) := mul_pos hk0 (by linarith)
    simp only
    linarith
  set β' : ℝ → Plane := fun t => if t ≤ σ then β t else A (ψ t) with hβ'def
  have hβ'eq1 : ∀ t ∈ Icc (0 : ℝ) σ, β' t = β t := fun t ht => if_pos ht.2
  have hβ'le : ∀ t, t ≤ σ → β' t = β t := fun t ht => if_pos ht
  have hβ'eq2 : ∀ t ∈ Icc σ L', β' t = A (ψ t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hβ'le σ le_rfl, hψσ, hσy]
    · rw [hβ'def]
      exact if_neg (not_le.2 h)
  -- continuity
  have hcont' : ContinuousOn β' (Icc 0 L') := by
    have h1 : ContinuousOn β' (Icc 0 σ) :=
      ContinuousOn.congr (hcont.mono (Icc_subset_Icc le_rfl hσ.2)) hβ'eq1
    have h2 : ContinuousOn β' (Icc σ L') := by
      refine ContinuousOn.congr ?_ hβ'eq2
      exact hA.cont.comp hψcont.continuousOn hψmaps
    have h := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hσ.1 hσL'.le] at h
  -- the image
  have himg : β' '' Icc 0 L' ⊆ β '' Icc 0 σ ∪ A '' Icc τ 1 := by
    rintro x ⟨t, ht, rfl⟩
    rcases le_or_gt t σ with h | h
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, (hβ'le t h).symm⟩
    · refine Or.inr ⟨ψ t, ⟨(hψgt t h).le, (hψmaps t ⟨h.le, ht.2⟩).2⟩, ?_⟩
      rw [hβ'eq2 t ⟨h.le, ht.2⟩]
  have himg0 : β' '' Icc 0 σ = β '' Icc 0 σ := by
    apply Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩; exact ⟨t, ht, (hβ'le t ht.2).symm⟩
    · rintro x ⟨t, ht, rfl⟩; exact ⟨t, ht, hβ'le t ht.2⟩
  -- injectivity
  have hinj' : InjOn β' (Icc 0 L') := by
    intro a ha b hb hab
    rcases le_or_gt a σ with hha | hha <;> rcases le_or_gt b σ with hhb | hhb
    · rw [hβ'le a hha, hβ'le b hhb] at hab
      exact hinj ⟨ha.1, le_trans hha hσ.2⟩ ⟨hb.1, le_trans hhb hσ.2⟩ hab
    · exfalso
      rw [hβ'le a hha, hβ'eq2 b ⟨hhb.le, hb.2⟩] at hab
      exact hafter (ψ b) (hψgt b hhb) (hψmaps b ⟨hhb.le, hb.2⟩).2
        ⟨a, ⟨ha.1, le_trans hha hσ.2⟩, hab⟩
    · exfalso
      rw [hβ'le b hhb, hβ'eq2 a ⟨hha.le, ha.2⟩] at hab
      exact hafter (ψ a) (hψgt a hha) (hψmaps a ⟨hha.le, ha.2⟩).2
        ⟨b, ⟨hb.1, le_trans hhb hσ.2⟩, hab.symm⟩
    · rw [hβ'eq2 a ⟨hha.le, ha.2⟩, hβ'eq2 b ⟨hhb.le, hb.2⟩] at hab
      have := hA.inj (hψmaps a ⟨hha.le, ha.2⟩) (hψmaps b ⟨hhb.le, hb.2⟩) hab
      exact hψmono.injOn ⟨hha.le, ha.2⟩ ⟨hhb.le, hb.2⟩ this
  refine ⟨⟨β', L', σ, m', hσ.1, hσL', hcont', hinj', ?_, ?_, ?_⟩,
    hmm', hsσ, hσ.2, ?_, ?_, ?_⟩
  · -- the new arc stays in `W 0`
    refine himg.trans (union_subset ?_ ?_)
    · exact (Set.image_mono (Icc_subset_Icc le_rfl hσ.2)).trans hsub
    · exact ((Set.image_mono (Icc_subset_Icc hτ01.1 le_rfl)).trans hAsub).trans
        (hWanti (Nat.zero_le m))
  · -- the endpoint lies in the deeper member
    rw [hβ'eq2 L' ⟨hσL'.le, le_rfl⟩, hψL', hA1]
    exact hv
  · -- the new stable part misses the deeper member
    rw [himg0]
    exact hdisjK.mono_right (Set.image_mono (Icc_subset_Icc le_rfl hσ.2))
  · -- the length estimate
    change L' - σ ≤ (L - s) / 2
    rw [hL'def]
    linarith
  · -- the stable part is unchanged
    exact fun t ht => hβ'le t ht
  · -- the new piece runs inside `W m`
    rintro x ⟨t, ht, rfl⟩
    change β' t ∈ W m
    rw [hβ'eq2 t ht]
    exact hAsub ⟨ψ t, hψmaps t ht, rfl⟩

/-- The initial approximating arc: an arc inside `W 0` from the prescribed point `x₀` to a
point of a member of the family which avoids `x₀`. -/
theorem exists_initial (hWopen : ∀ n, IsOpen (W n)) (hWconn : ∀ n, IsPreconnected (W n))
    (hWne : ∀ n, (W n).Nonempty) (hWanti : Antitone W)
    (hWsmall : ∀ ε > 0, ∃ n, W n ⊆ ball z ε) (hz : z ∉ W 0)
    {x₀ : Plane} (hx₀ : x₀ ∈ W 0) :
    ∃ st : ArcApprox W, st.param 0 = x₀ ∧ st.stab = 0 := by
  have hxz : x₀ ≠ z := fun h => hz (h ▸ hx₀)
  have hdist : 0 < dist z x₀ := dist_pos.2 (Ne.symm hxz)
  obtain ⟨n₀, hn₀⟩ := hWsmall _ hdist
  have hx₀n : x₀ ∉ W n₀ := by
    intro h
    have h' := hn₀ h
    rw [mem_ball, dist_comm] at h'
    exact lt_irrefl _ h'
  obtain ⟨v, hv⟩ := hWne n₀
  have hne : x₀ ≠ v := fun h => hx₀n (h ▸ hv)
  have hvW0 : v ∈ W 0 := hWanti (Nat.zero_le n₀) hv
  obtain ⟨A, hA, hA0, hA1, hAsub⟩ := exists_arc_in_open (hWopen 0) (hWconn 0) hx₀ hvW0 hne
  refine ⟨⟨A, 1, 0, n₀, le_refl 0, zero_lt_one, hA.cont, hA.inj, hAsub,
    by rw [hA1]; exact hv, ?_⟩, hA0, rfl⟩
  rw [Set.disjoint_right]
  rintro x ⟨t, ht, rfl⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  rw [ht0, hA0]
  exact hx₀n

/-- **Accessibility of the limit point of a nested family of domains.**

If `W 0 ⊇ W 1 ⊇ ⋯` is a decreasing sequence of non-empty open connected subsets of the
plane which shrink to a point `z` (every ball around `z` contains some `W n`) and if `z`
does not belong to `W 0`, then `z` is accessible from `W 0`: every point `x₀` of `W 0` is
the starting point of an arc which ends at `z` and whose other points all lie in `W 0`.

This is the topological core of the accessibility assertion of Theorem 4 of
Klein–Langetepe–Nilforoushan (2009): once a complementary domain of a Jordan curve is known
to be locally connected at a boundary point `z`, the sets `W n` are produced by
intersecting it with small balls around `z`, and the theorem yields the access arc. -/
theorem exists_arc_to_limit (hWopen : ∀ n, IsOpen (W n)) (hWconn : ∀ n, IsPreconnected (W n))
    (hWne : ∀ n, (W n).Nonempty) (hWanti : Antitone W)
    (hWsmall : ∀ ε > 0, ∃ n, W n ⊆ ball z ε) (hz : z ∉ W 0)
    {x₀ : Plane} (hx₀ : x₀ ∈ W 0) :
    ∃ γ : ℝ → Plane, IsArc γ ∧ γ 0 = x₀ ∧ γ 1 = z ∧ γ '' Ico 0 1 ⊆ W 0 := by
  classical
  obtain ⟨st₀, hst₀0, hst₀s⟩ := exists_initial hWopen hWconn hWne hWanti hWsmall hz hx₀
  have hstep : ∀ st : ArcApprox W, ∃ st' : ArcApprox W, st.Link st' :=
    fun st => exists_link hWopen hWconn hWne hWanti hWsmall hz st
  choose F hF using hstep
  set seq : ℕ → ArcApprox W := fun n => F^[n] st₀ with hseqdef
  have hseq0 : seq 0 = st₀ := rfl
  have hseqsucc : ∀ n, seq (n + 1) = F (seq n) := fun n =>
    Function.iterate_succ_apply' F n st₀
  have hlink : ∀ n, (seq n).Link (seq (n + 1)) := by
    intro n
    rw [hseqsucc n]
    exact hF (seq n)
  -- the basic monotonicity properties of the construction
  have hidx : StrictMono fun n => (seq n).idx :=
    strictMono_nat_of_lt_succ fun n => (hlink n).1
  have hstab : StrictMono fun n => (seq n).stab :=
    strictMono_nat_of_lt_succ fun n => (hlink n).2.1
  have hstabL : ∀ n, (seq (n + 1)).stab ≤ (seq n).len := fun n => (hlink n).2.2.1
  have hlenle : ∀ n, (seq (n + 1)).len - (seq (n + 1)).stab ≤
      ((seq n).len - (seq n).stab) / 2 := fun n => (hlink n).2.2.2.1
  have hagree1 : ∀ n, ∀ t ≤ (seq (n + 1)).stab, (seq (n + 1)).param t = (seq n).param t :=
    fun n => (hlink n).2.2.2.2.1
  have htail1 : ∀ n, (seq (n + 1)).param '' Icc (seq (n + 1)).stab (seq (n + 1)).len ⊆
      W (seq n).idx := fun n => (hlink n).2.2.2.2.2
  -- the stable times are bounded
  have hQ : ∀ n, (seq (n + 1)).stab + 2 * ((seq (n + 1)).len - (seq (n + 1)).stab) ≤
      (seq n).stab + 2 * ((seq n).len - (seq n).stab) := by
    intro n
    have h1 := hstabL n
    have h2 := hlenle n
    linarith
  have hQanti : Antitone fun n => (seq n).stab + 2 * ((seq n).len - (seq n).stab) :=
    antitone_nat_of_succ_le hQ
  have hbound : ∀ n, (seq n).stab ≤ (seq 0).stab + 2 * ((seq 0).len - (seq 0).stab) := by
    intro n
    have h1 : (seq n).stab ≤ (seq n).stab + 2 * ((seq n).len - (seq n).stab) := by
      have := (seq n).stab_lt
      linarith
    exact h1.trans (hQanti (Nat.zero_le n))
  have hbdd : BddAbove (range fun n => (seq n).stab) := by
    refine ⟨(seq 0).stab + 2 * ((seq 0).len - (seq 0).stab), ?_⟩
    rintro x ⟨n, rfl⟩
    exact hbound n
  set S : ℝ := ⨆ n, (seq n).stab with hSdef
  have hstabS : ∀ n, (seq n).stab < S :=
    fun n => lt_of_lt_of_le (hstab (Nat.lt_succ_self n)) (le_ciSup hbdd (n + 1))
  have hstab0 : (seq 0).stab = 0 := by rw [hseq0]; exact hst₀s
  have hS0 : 0 < S := by
    have := hstabS 0
    rwa [hstab0] at this
  -- the arcs agree on the stable parts
  have hagree : ∀ j n, j ≤ n → ∀ t ≤ (seq j).stab, (seq n).param t = (seq j).param t := by
    intro j n hjn
    induction n with
    | zero =>
        intro t _
        have : j = 0 := Nat.le_zero.1 hjn
        rw [this]
    | succ n ih =>
        intro t ht
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hjn) with h | h
        · have hjn' : j ≤ n := Nat.lt_succ_iff.1 h
          have h1 : t ≤ (seq (n + 1)).stab :=
            ht.trans (hstab.monotone (Nat.le_succ_of_le hjn'))
          rw [hagree1 n t h1]
          exact ih hjn' t ht
        · rw [h]
  -- the index of the approximating arc used at a given parameter
  set N : ℝ → ℕ := fun t => sInf {n | t < (seq n).stab} with hNdef
  have hNex : ∀ t, t < S → {n | t < (seq n).stab}.Nonempty := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup ht
    exact ⟨n, hn⟩
  have hNmem : ∀ t, t < S → t < (seq (N t)).stab := by
    intro t ht
    exact Nat.sInf_mem (hNex t ht)
  have hNle : ∀ t n, t < (seq n).stab → N t ≤ n := fun t n hn => Nat.sInf_le hn
  set γ₀ : ℝ → Plane := fun t => if t < S then (seq (N t)).param t else z with hγ₀def
  have hkey : ∀ n t, t < (seq n).stab → γ₀ t = (seq n).param t := by
    intro n t ht
    have htS : t < S := ht.trans (hstabS n)
    rw [hγ₀def]
    simp only [if_pos htS]
    exact (hagree (N t) n (hNle t n ht) t (hNmem t htS).le).symm
  have hγ₀S : γ₀ S = z := by
    rw [hγ₀def]
    simp
  have himage : ∀ t, 0 ≤ t → t < S → γ₀ t ∈ W 0 := by
    intro t ht0 htS
    obtain ⟨n, hn⟩ := hNex t htS
    rw [hkey n t hn]
    exact (seq n).sub ⟨t, ⟨ht0, hn.le.trans (seq n).stab_lt.le⟩, rfl⟩
  -- the tail of each approximating arc stays in a deep member of the family
  have htail : ∀ k n, k + 1 ≤ n →
      (seq n).param '' Icc (seq (k + 1)).stab (seq n).len ⊆ W (seq k).idx := by
    intro k n hkn
    induction n with
    | zero => exact absurd hkn (by omega)
    | succ n ih =>
        rcases Nat.lt_or_ge k n with h | h
        · have hkn' : k + 1 ≤ n := h
          rintro x ⟨t, ht, rfl⟩
          rcases le_or_gt t (seq (n + 1)).stab with hle | hgt
          · rw [hagree1 n t hle]
            exact ih hkn' ⟨t, ⟨ht.1, hle.trans (hstabL n)⟩, rfl⟩
          · have := htail1 n ⟨t, ⟨hgt.le, ht.2⟩, rfl⟩
            exact hWanti (hidx.monotone (by omega : k ≤ n)) this
        · have hkn' : k = n := by omega
          subst hkn'
          exact htail1 k
  have hγtail : ∀ k t, (seq (k + 1)).stab ≤ t → t < S → γ₀ t ∈ W (seq k).idx := by
    intro k t htk htS
    obtain ⟨n, hn⟩ := hNex t htS
    have hkn : k + 1 ≤ n := by
      by_contra hcon
      have hle : (seq n).stab ≤ (seq (k + 1)).stab := hstab.monotone (by omega)
      exact absurd (lt_of_le_of_lt htk (lt_of_lt_of_le hn hle)) (lt_irrefl _)
    rw [hkey n t hn]
    exact htail k n hkn ⟨t, ⟨htk, hn.le.trans (seq n).stab_lt.le⟩, rfl⟩
  -- continuity of the limit
  have hcont₀ : ContinuousOn γ₀ (Icc 0 S) := by
    intro t₀ ht₀
    rcases eq_or_lt_of_le ht₀.2 with hEq | hlt
    · -- at the endpoint
      subst hEq
      rw [ContinuousWithinAt, hγ₀S]
      refine Metric.tendsto_nhdsWithin_nhds.2 ?_
      intro ε hε
      obtain ⟨n₁, hn₁⟩ := hWsmall ε hε
      have hkidx : n₁ ≤ (seq n₁).idx := hidx.le_apply
      refine ⟨S - (seq (n₁ + 1)).stab, by linarith [hstabS (n₁ + 1)], ?_⟩
      intro x hx hdist
      rcases eq_or_lt_of_le hx.2 with hxS | hxS
      · rw [hxS, hγ₀S]
        simpa using hε
      · have hxk : (seq (n₁ + 1)).stab ≤ x := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.2])] at hdist
          linarith
        have := hγtail n₁ x hxk hxS
        have hsub : W (seq n₁).idx ⊆ ball z ε := (hWanti hkidx).trans hn₁
        have hmem := hsub this
        rw [mem_ball] at hmem
        exact hmem
    · -- at an interior parameter
      obtain ⟨n, hn⟩ := hNex t₀ hlt
      have hmemA : t₀ ∈ Icc 0 S ∩ Iio (seq n).stab := ⟨ht₀, hn⟩
      have hsubA : Icc 0 S ∩ Iio (seq n).stab ⊆ Icc 0 (seq n).len := by
        rintro x ⟨hx1, hx2⟩
        exact ⟨hx1.1, hx2.le.trans (seq n).stab_lt.le⟩
      have hcw : ContinuousWithinAt (seq n).param (Icc 0 S ∩ Iio (seq n).stab) t₀ :=
        ((seq n).cont.mono hsubA).continuousWithinAt hmemA
      have heq : EqOn γ₀ (seq n).param (Icc 0 S ∩ Iio (seq n).stab) := by
        intro x hx
        exact hkey n x hx.2
      have h2 : ContinuousWithinAt γ₀ (Icc 0 S ∩ Iio (seq n).stab) t₀ :=
        hcw.congr heq (heq hmemA)
      exact (continuousWithinAt_inter (Iio_mem_nhds hn)).1 h2
  -- injectivity of the limit
  have hinj₀ : InjOn γ₀ (Icc 0 S) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le ha.2 with haS | haS
    · rcases eq_or_lt_of_le hb.2 with hbS | hbS
      · rw [haS, hbS]
      · exfalso
        rw [haS, hγ₀S] at hab
        exact hz (hab ▸ himage b hb.1 hbS)
    · rcases eq_or_lt_of_le hb.2 with hbS | hbS
      · exfalso
        rw [hbS, hγ₀S] at hab
        exact hz (hab.symm ▸ himage a ha.1 haS)
      · obtain ⟨n, hn⟩ := hNex a haS
        obtain ⟨n', hn'⟩ := hNex b hbS
        have hna : a < (seq (max n n')).stab :=
          lt_of_lt_of_le hn (hstab.monotone (le_max_left n n'))
        have hnb : b < (seq (max n n')).stab :=
          lt_of_lt_of_le hn' (hstab.monotone (le_max_right n n'))
        rw [hkey _ a hna, hkey _ b hnb] at hab
        exact (seq (max n n')).inj
          ⟨ha.1, hna.le.trans (seq (max n n')).stab_lt.le⟩
          ⟨hb.1, hnb.le.trans (seq (max n n')).stab_lt.le⟩ hab
  -- rescaling the parameter interval to `[0,1]`
  refine ⟨fun t => γ₀ (S * t), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine hcont₀.comp (by fun_prop) ?_
    rintro t ht
    exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  · intro a ha b hb hab
    have hma : S * a ∈ Icc 0 S := ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩
    have hmb : S * b ∈ Icc 0 S := ⟨by nlinarith [hb.1, hb.2], by nlinarith [hb.1, hb.2]⟩
    exact mul_left_cancel₀ (ne_of_gt hS0) (hinj₀ hma hmb hab)
  · have h0 : (0 : ℝ) < (seq 1).stab := by
      have h : (seq 0).stab < (seq 1).stab := hstab Nat.zero_lt_one
      rwa [hstab0] at h
    change γ₀ (S * 0) = x₀
    rw [mul_zero, hkey 1 0 h0, hagree 0 1 (Nat.zero_le 1) 0 (by rw [hstab0]), hseq0,
      hst₀0]
  · change γ₀ (S * 1) = z
    rw [mul_one, hγ₀S]
  · rintro x ⟨t, ht, rfl⟩
    exact himage (S * t) (by nlinarith [ht.1]) (by nlinarith [ht.1, ht.2])

end Construction

end AVD
