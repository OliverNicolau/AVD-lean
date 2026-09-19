import AbstractVoronoi.Jordan.CircleParam

/-!
# Circular crosscuts

Let `D` be an open subset of the plane and let `S(z,r)` be a circle which is neither
contained in `D` nor disjoint from it.  Cutting the circle at the points of `S(z,r) ∖ D`
leaves a family of open circular arcs inside `D`; the main result of this file,
`AVD.exists_circular_crosscut`, produces such an arc through a prescribed point
`w ∈ D ∩ S(z,r)`: an arc `κ` contained in the circle, whose relative interior lies in `D`
and contains `w`, and whose two (distinct) endpoints lie on the frontier of `D`.

When `D` is a complementary domain of a closed Jordan curve `C`, the frontier of `D` is `C`,
so `κ` is a *crosscut of `D`* in the sense of `AbstractVoronoi.Jordan.Crosscut`, of diameter at
most `2r`.  This is the mechanism that produces crosscuts of arbitrarily small diameter
near a given point of `C`, which is what the local (Jordan–Schönflies) part of **Theorem 4**
of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902

requires.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- **Circular crosscuts.**  Let `D` be open, let `w ∈ D` lie on the circle `S(z,r)` and
assume that the circle contains at least two points outside `D`.  Then the connected
component of `w` in `D ∩ S(z,r)` is an open circular arc: there is an arc `κ` contained in
`S(z,r)`, with `κ` minus its endpoints contained in `D` and containing `w`, and with two
distinct endpoints on the frontier of `D`.

Applied to a complementary domain `D` of a closed Jordan curve `C` (whose frontier is `C`),
this produces a crosscut of `D` of diameter at most `2r`, the tool for the local part of
**Theorem 4** of Klein–Langetepe–Nilforoushan (2009). -/
theorem exists_circular_crosscut {D : Set Plane} (hD : IsOpen D)
    {z : Plane} {r : ℝ} (hr : 0 < r) {w : Plane} (hwD : w ∈ D) (hw : w ∈ sphere z r)
    (h2 : (sphere z r \ D).Nontrivial) :
    ∃ κ : ℝ → Plane, IsArc κ ∧ κ '' Icc 0 1 ⊆ sphere z r ∧ κ '' Ioo 0 1 ⊆ D ∧
      w ∈ κ '' Ioo 0 1 ∧ κ 0 ∈ frontier D ∧ κ 1 ∈ frontier D ∧ κ 0 ≠ κ 1 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set P : ℝ → Plane := circleParam z r with hP
  have hPcont : Continuous P := continuous_circleParam z r
  have hPsph : ∀ t, P t ∈ sphere z r := fun t => circleParam_mem_sphere hr.le t
  have hPper : ∀ (t : ℝ) (n : ℤ), P (t + n * (2 * Real.pi)) = P t :=
    fun t n => circleParam_periodic_int z r t n
  have hPeq : ∀ s t : ℝ, P s = P t ↔ ∃ n : ℤ, s = t + n * (2 * Real.pi) :=
    fun s t => circleParam_eq_iff hrne s t
  have hPsurj : ∀ y ∈ sphere z r, ∃ t : ℝ, P t = y :=
    fun y hy => exists_circleParam_eq hr hy
  -- the parameter set of the points of the circle outside `D`
  set Wc : Set ℝ := {t | P t ∉ D} with hWc
  have hWcmem : ∀ t : ℝ, t ∈ Wc ↔ P t ∉ D := fun _ => Iff.rfl
  have hWcClosed : IsClosed Wc := (hD.isClosed_compl).preimage hPcont
  have hWcshift : ∀ t ∈ Wc, ∀ n : ℤ, t + n * (2 * Real.pi) ∈ Wc := by
    intro t ht n
    rw [hWcmem, hPper]
    exact ht
  obtain ⟨q₁, hq₁, q₂, hq₂, hq₁₂⟩ := h2
  obtain ⟨s₁, hs₁⟩ := hPsurj q₁ hq₁.1
  have hs₁Wc : s₁ ∈ Wc := by rw [hWcmem, hs₁]; exact hq₁.2
  -- the parameter of `w`
  obtain ⟨t₀, ht₀⟩ := hPsurj w hw
  have ht₀D : P t₀ ∈ D := by rw [ht₀]; exact hwD
  have ht₀Wc : t₀ ∉ Wc := fun h => (hWcmem t₀).1 h ht₀D
  -- points of `Wc` on both sides of `t₀`
  have hbelow : ∃ s ∈ Wc, s ≤ t₀ := by
    obtain ⟨n, hn⟩ := exists_int_lt ((t₀ - s₁) / (2 * Real.pi))
    refine ⟨s₁ + n * (2 * Real.pi), hWcshift s₁ hs₁Wc n, ?_⟩
    have := (lt_div_iff₀ hpi).mp hn
    linarith
  have habove : ∃ s ∈ Wc, t₀ ≤ s := by
    obtain ⟨n, hn⟩ := exists_int_gt ((t₀ - s₁) / (2 * Real.pi))
    refine ⟨s₁ + n * (2 * Real.pi), hWcshift s₁ hs₁Wc n, ?_⟩
    have := (div_lt_iff₀ hpi).mp hn
    linarith
  -- the endpoints of the component of `t₀`
  set S₁ : Set ℝ := Wc ∩ Iic t₀ with hS₁def
  set S₂ : Set ℝ := Wc ∩ Ici t₀ with hS₂def
  have hS₁ne : S₁.Nonempty := by obtain ⟨s, hs, hle⟩ := hbelow; exact ⟨s, hs, hle⟩
  have hS₂ne : S₂.Nonempty := by obtain ⟨s, hs, hle⟩ := habove; exact ⟨s, hs, hle⟩
  have hS₁closed : IsClosed S₁ := hWcClosed.inter isClosed_Iic
  have hS₂closed : IsClosed S₂ := hWcClosed.inter isClosed_Ici
  have hS₁bdd : BddAbove S₁ := ⟨t₀, fun x hx => hx.2⟩
  have hS₂bdd : BddBelow S₂ := ⟨t₀, fun x hx => hx.2⟩
  set α : ℝ := sSup S₁ with hαdef
  set β : ℝ := sInf S₂ with hβdef
  have hαmem : α ∈ S₁ := hS₁closed.csSup_mem hS₁ne hS₁bdd
  have hβmem : β ∈ S₂ := hS₂closed.csInf_mem hS₂ne hS₂bdd
  have hαlt : α < t₀ :=
    lt_of_le_of_ne (mem_Iic.1 hαmem.2) (fun h => ht₀Wc (by rw [← h]; exact hαmem.1))
  have hβgt : t₀ < β :=
    lt_of_le_of_ne (mem_Ici.1 hβmem.2) (fun h => ht₀Wc (by rw [h]; exact hβmem.1))
  have hαβ : α < β := lt_trans hαlt hβgt
  have hβαpos : 0 < β - α := by linarith
  -- between `α` and `β` the circle stays in `D`
  have hIoo : ∀ t ∈ Ioo α β, P t ∈ D := by
    intro t ht
    by_contra hnot
    have htWc : t ∈ Wc := hnot
    rcases le_or_gt t t₀ with h | h
    · have : t ≤ α := le_csSup hS₁bdd ⟨htWc, h⟩
      exact absurd ht.1 (not_lt.2 this)
    · have : β ≤ t := csInf_le hS₂bdd ⟨htWc, h.le⟩
      exact absurd ht.2 (not_lt.2 this)
  -- the component has parameter length `< 2π`
  have hlen : β - α < 2 * Real.pi := by
    by_contra hnot
    rw [not_lt] at hnot
    have hsub : sphere z r \ D ⊆ {P α} := by
      rintro y ⟨hysph, hyD⟩
      obtain ⟨t, ht⟩ := hPsurj y hysph
      set n : ℤ := ⌈(α - t) / (2 * Real.pi)⌉ with hn
      have hu : ((α - t) / (2 * Real.pi)) * (2 * Real.pi) = α - t := by field_simp
      have hle : ((α - t) / (2 * Real.pi)) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right (Int.le_ceil _) hpi.le
      rw [hu] at hle
      have hlt2 : (n : ℝ) * (2 * Real.pi) <
          (((α - t) / (2 * Real.pi)) + 1) * (2 * Real.pi) :=
        mul_lt_mul_of_pos_right (Int.ceil_lt_add_one _) hpi
      have hrhs : (((α - t) / (2 * Real.pi)) + 1) * (2 * Real.pi) = (α - t) + 2 * Real.pi := by
        field_simp
      rw [hrhs] at hlt2
      have hPt : P (t + n * (2 * Real.pi)) = y := by rw [hPper]; exact ht
      rcases eq_or_lt_of_le (by linarith : α ≤ t + (n : ℝ) * (2 * Real.pi)) with heq | hlt
      · exact mem_singleton_iff.2 (by rw [← hPt, ← heq])
      · exact absurd (hPt ▸ hIoo _ ⟨hlt, by linarith⟩) hyD
    exact hq₁₂ ((hsub hq₁).trans (hsub hq₂).symm)
  -- the arc
  set κ : ℝ → Plane := fun t => P (α + t * (β - α)) with hκdef
  have hκ0 : κ 0 = P α := by simp [hκdef]
  have hκ1 : κ 1 = P β := by simp [hκdef]
  have hmem : ∀ x ∈ Icc (0 : ℝ) 1, α + x * (β - α) ∈ Icc α β := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2]
  refine ⟨κ, ⟨(hPcont.comp (by fun_prop)).continuousOn, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    have h := circleParam_injOn (z := z) hrne hlen (hmem s hs) (hmem t ht) hst
    exact mul_right_cancel₀ (ne_of_gt hβαpos) (by linarith)
  · rintro y ⟨t, -, rfl⟩
    exact hPsph _
  · rintro y ⟨t, ht, rfl⟩
    exact hIoo _ ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  · refine ⟨(t₀ - α) / (β - α), ⟨div_pos (by linarith) hβαpos,
      (div_lt_one hβαpos).2 (by linarith)⟩, ?_⟩
    change P (α + (t₀ - α) / (β - α) * (β - α)) = w
    rw [div_mul_cancel₀ _ (ne_of_gt hβαpos)]
    simpa using ht₀
  · -- the endpoint `κ 0 = P α` is on the frontier of `D`
    have hcl : P α ∈ closure D := by
      have htend : Filter.Tendsto P (𝓝[>] α) (𝓝 (P α)) :=
        (hPcont.tendsto α).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsGT hαβ] with s hs using hIoo s hs
    rw [hD.frontier_eq, hκ0]
    exact ⟨hcl, hαmem.1⟩
  · have hcl : P β ∈ closure D := by
      have htend : Filter.Tendsto P (𝓝[<] β) (𝓝 (P β)) :=
        (hPcont.tendsto β).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsLT hαβ] with s hs using hIoo s hs
    rw [hD.frontier_eq, hκ1]
    exact ⟨hcl, hβmem.1⟩
  · rw [hκ0, hκ1]
    intro hcontra
    obtain ⟨n, hn⟩ := (hPeq α β).1 hcontra
    have hn0 : (n : ℝ) * (2 * Real.pi) < 0 := by linarith
    have hn1 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by linarith
    have hnlt : (n : ℝ) < 0 := by nlinarith
    have hngt : (-1 : ℝ) < n := by nlinarith
    have hz : n = 0 := by
      have h1 : n < 0 := by exact_mod_cast hnlt
      have h2 : (-1 : ℤ) < n := by exact_mod_cast hngt
      omega
    rw [hz] at hn
    simp at hn
    linarith

end AVD
