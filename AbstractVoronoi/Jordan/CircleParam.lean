import AbstractVoronoi.Jordan.Arcs

/-!
# The parametrized circle of the plane

This file provides the standard parametrization

`circleParam z r t = z + r · (cos t, sin t)`

of the circle of centre `z` and radius `r` of the plane, together with the facts about it
needed to cut *circular crosscuts* out of a complementary domain of a closed Jordan curve:
the parametrization is continuous, `2π`-periodic, injective on every parameter interval of
length `< 2π`, its image is exactly the sphere `Metric.sphere z r`, and every point of that
sphere is attained.

Circular crosscuts are the tool by which small crosscuts near a prescribed point of a closed
Jordan curve are produced, in the approach to the local (Jordan–Schönflies) part of
**Theorem 4** of

* R. Klein, E. Langetepe, Z. Nilforoushan, *Abstract Voronoi diagrams revisited*,
  Computational Geometry 42 (2009) 885–902.

The plane is identified with `ℂ` through the isometry `Complex.orthonormalBasisOneI.repr`,
which is what makes the elementary trigonometry of the circle available.
-/

noncomputable section

open Set Topology Metric

namespace AVD

/-- The isometric identification of `ℂ` with the plane `ℝ²` used to parametrize circles. -/
def ofComplex : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

/-- The standard parametrization `t ↦ z + r · (cos t, sin t)` of the circle of centre `z`
and radius `r` of the plane. -/
def circleParam (z : Plane) (r : ℝ) (t : ℝ) : Plane :=
  z + r • ofComplex (Complex.exp (t * Complex.I))

/-- The standard parametrization of a circle is continuous. -/
theorem continuous_circleParam (z : Plane) (r : ℝ) : Continuous (circleParam z r) := by
  unfold circleParam
  fun_prop

/-- Every point of the standard parametrization of the circle of centre `z` and radius `r`
is at distance `|r|` from `z`. -/
theorem dist_circleParam (z : Plane) (r : ℝ) (t : ℝ) :
    dist (circleParam z r t) z = |r| := by
  have h : ‖ofComplex (Complex.exp (t * Complex.I))‖ = 1 := by
    rw [ofComplex, LinearIsometryEquiv.norm_map, Complex.norm_exp_ofReal_mul_I]
  simp [circleParam, dist_eq_norm, norm_smul, h]

/-- The standard parametrization of the circle of centre `z` and radius `r ≥ 0` takes its
values on that circle. -/
theorem circleParam_mem_sphere {z : Plane} {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    circleParam z r t ∈ sphere z r := by
  have h := dist_circleParam z r t
  rw [abs_of_nonneg hr] at h
  exact h

/-- The standard parametrization of a circle is invariant under integer multiples of `2π`. -/
theorem circleParam_periodic_int (z : Plane) (r : ℝ) (t : ℝ) (n : ℤ) :
    circleParam z r (t + n * (2 * Real.pi)) = circleParam z r t := by
  have h : Complex.exp (((t + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨n, by push_cast; ring⟩
  unfold circleParam
  rw [h]

/-- The standard parametrization of a circle is `2π`-periodic. -/
theorem circleParam_periodic (z : Plane) (r : ℝ) (t : ℝ) :
    circleParam z r (t + 2 * Real.pi) = circleParam z r t := by
  simpa using circleParam_periodic_int z r t 1

/-- Two parameters give the same point of the circle exactly when they differ by a multiple
of `2π`. -/
theorem circleParam_eq_iff {z : Plane} {r : ℝ} (hr : r ≠ 0) (s t : ℝ) :
    circleParam z r s = circleParam z r t ↔ ∃ n : ℤ, s = t + n * (2 * Real.pi) := by
  constructor
  · intro h
    have h1 : (r : ℝ) • ofComplex (Complex.exp (s * Complex.I)) =
        r • ofComplex (Complex.exp (t * Complex.I)) := by
      have := h
      unfold circleParam at this
      exact add_left_cancel this
    have h2 : ofComplex (Complex.exp (s * Complex.I)) =
        ofComplex (Complex.exp (t * Complex.I)) := smul_right_injective _ hr h1
    have h3 : Complex.exp (s * Complex.I) = Complex.exp (t * Complex.I) :=
      ofComplex.injective h2
    rw [Complex.exp_eq_exp_iff_exists_int] at h3
    obtain ⟨n, hn⟩ := h3
    refine ⟨n, ?_⟩
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    have : ((s : ℂ)) = (t : ℂ) + n * (2 * Real.pi) := by
      have hn' : (s : ℂ) * Complex.I = ((t : ℂ) + n * (2 * Real.pi)) * Complex.I := by
        rw [hn]; ring
      exact mul_right_cancel₀ hI hn'
    exact_mod_cast this
  · rintro ⟨n, rfl⟩
    exact circleParam_periodic_int z r t n

/-- The parametrization of the circle is injective on every parameter interval of length
`< 2π`. -/
theorem circleParam_injOn {z : Plane} {r : ℝ} (hr : r ≠ 0) {a b : ℝ}
    (hab : b - a < 2 * Real.pi) : InjOn (circleParam z r) (Icc a b) := by
  intro s hs t ht hst
  obtain ⟨n, hn⟩ := (circleParam_eq_iff hr s t).1 hst
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlt : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    have h1 : |(n : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
      rw [abs_lt]
      constructor <;> [nlinarith [hs.1, hs.2, ht.1, ht.2]; nlinarith [hs.1, hs.2, ht.1, ht.2]]
    rwa [abs_mul, abs_of_pos hpi] at h1
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (by omega)
    nlinarith
  simp [hn0] at hn
  linarith

/-- Every point of the circle of centre `z` and radius `r > 0` is attained by the
parametrization. -/
theorem exists_circleParam_eq {z : Plane} {r : ℝ} (hr : 0 < r) {w : Plane}
    (hw : w ∈ sphere z r) : ∃ t : ℝ, circleParam z r t = w := by
  set u : ℂ := ofComplex.symm (r⁻¹ • (w - z)) with hu
  have hnorm : ‖u‖ = 1 := by
    rw [hu, LinearIsometryEquiv.norm_map, norm_smul]
    have : ‖w - z‖ = r := by
      have := mem_sphere.1 hw
      rwa [dist_eq_norm] at this
    rw [this]
    simp [abs_of_pos hr, inv_mul_cancel₀ (ne_of_gt hr)]
  refine ⟨u.arg, ?_⟩
  have hkey : Complex.exp (u.arg * Complex.I) = u := by
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hnorm] at this
    simpa using this
  rw [circleParam, hkey, hu, LinearIsometryEquiv.apply_symm_apply, smul_smul,
    mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  abel

/-- The image of the parametrization is exactly the circle. -/
theorem range_circleParam {z : Plane} {r : ℝ} (hr : 0 < r) :
    range (circleParam z r) = sphere z r := by
  apply Subset.antisymm
  · rintro w ⟨t, rfl⟩
    exact circleParam_mem_sphere hr.le t
  · intro w hw
    obtain ⟨t, ht⟩ := exists_circleParam_eq hr hw
    exact ⟨t, ht⟩

end AVD
