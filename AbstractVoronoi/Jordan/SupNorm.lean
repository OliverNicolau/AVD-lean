import AbstractVoronoi.Imports

/-!
# The sup norm of the plane and the model square

The sup norm `‖x‖∞ = max |x₀| |x₁|` of the plane, the axis-parallel squares it defines, and
the **model curve** `{x | ‖x‖∞ = 1}`, the boundary of the square `[-1,1]²`.  They are used in
`AbstractVoronoi/Jordan/SchoenfliesClosed.lean`, where a closed Jordan curve is carried onto
the model curve by a homeomorphism of the plane.

The definitions and the elementary facts below follow `Schoenflies/Square.lean` of

* Á. Begué, *The Jordan–Schönflies theorem in Lean*,
  <https://github.com/alonamaloh/schoenflies-lean> (Apache License 2.0),

restricted to what this development uses.
-/

noncomputable section

open Set

namespace AVD

namespace Square

/-- The plane, written out (this file sits below `AbstractVoronoi/Jordan/Sphere.lean`, where
the abbreviation `AVD.Plane` is introduced; the two are the same type). -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The sup norm `‖x‖∞ = max |x₀| |x₁|`. -/
def supNorm (x : ℝ²) : ℝ := max |x 0| |x 1|

/-- The sup distance. -/
def supDist (x y : ℝ²) : ℝ := supNorm (x - y)

/-- The closed axis-parallel square of radius `r` about `c`. -/
def closedSquare (c : ℝ²) (r : ℝ) : Set ℝ² := {x | supDist x c ≤ r}

/-- The open axis-parallel square of radius `r` about `c`. -/
def openSquare (c : ℝ²) (r : ℝ) : Set ℝ² := {x | supDist x c < r}

/-- The model curve: the boundary of the square `[-1,1]²`. -/
def modelCurve : Set ℝ² := {x | supNorm x = 1}

theorem supNorm_nonneg (x : ℝ²) : 0 ≤ supNorm x :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem abs_zero_le_supNorm (x : ℝ²) : |x 0| ≤ supNorm x := le_max_left _ _

theorem abs_one_le_supNorm (x : ℝ²) : |x 1| ≤ supNorm x := le_max_right _ _

/-- The sup distance satisfies the triangle inequality. -/
theorem supDist_triangle (x y z : ℝ²) : supDist x z ≤ supDist x y + supDist y z := by
  simp only [supDist, supNorm, PiLp.sub_apply]
  refine max_le ?_ ?_
  · calc |x 0 - z 0| ≤ |x 0 - y 0| + |y 0 - z 0| := abs_sub_le _ _ _
      _ ≤ max |x 0 - y 0| |x 1 - y 1| + max |y 0 - z 0| |y 1 - z 1| :=
          add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc |x 1 - z 1| ≤ |x 1 - y 1| + |y 1 - z 1| := abs_sub_le _ _ _
      _ ≤ max |x 0 - y 0| |x 1 - y 1| + max |y 0 - z 0| |y 1 - z 1| :=
          add_le_add (le_max_right _ _) (le_max_right _ _)

theorem norm_sq_eq (x : ℝ²) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_two]

/-- The sup norm is at most the Euclidean norm. -/
theorem supNorm_le_norm (x : ℝ²) : supNorm x ≤ ‖x‖ := by
  have h0 : |x 0| ≤ ‖x‖ := by
    have : |x 0| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 1)]
    nlinarith [abs_nonneg (x 0), norm_nonneg x]
  have h1 : |x 1| ≤ ‖x‖ := by
    have : |x 1| ^ 2 ≤ ‖x‖ ^ 2 := by rw [sq_abs, norm_sq_eq]; nlinarith [sq_nonneg (x 0)]
    nlinarith [abs_nonneg (x 1), norm_nonneg x]
  exact max_le h0 h1

/-- The Euclidean norm is at most `√2` times the sup norm. -/
theorem norm_le_sqrt_two_mul_supNorm (x : ℝ²) : ‖x‖ ≤ Real.sqrt 2 * supNorm x := by
  have h0 : x 0 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_zero_le_supNorm x, abs_nonneg (x 0)]
  have h1 : x 1 ^ 2 ≤ supNorm x ^ 2 := by
    rw [← sq_abs]; nlinarith [abs_one_le_supNorm x, abs_nonneg (x 1)]
  have hbound : ‖x‖ ^ 2 ≤ (Real.sqrt 2 * supNorm x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), norm_sq_eq]
    linarith
  nlinarith [norm_nonneg x, mul_nonneg (Real.sqrt_nonneg 2) (supNorm_nonneg x)]

/-- The sup norm is continuous. -/
theorem continuous_supNorm : Continuous supNorm := by
  unfold supNorm
  have h0 : Continuous fun x : ℝ² => x 0 := PiLp.continuous_apply _ _ 0
  have h1 : Continuous fun x : ℝ² => x 1 := PiLp.continuous_apply _ _ 1
  fun_prop

/-- The sup norm is convex. -/
theorem convexOn_supNorm : ConvexOn ℝ univ supNorm := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc : ∀ i : Fin 2, |(a • x + b • y) i| ≤ a * supNorm x + b * supNorm y := by
    intro i
    have hx : |x i| ≤ supNorm x := by
      fin_cases i
      · exact abs_zero_le_supNorm x
      · exact abs_one_le_supNorm x
    have hy : |y i| ≤ supNorm y := by
      fin_cases i
      · exact abs_zero_le_supNorm y
      · exact abs_one_le_supNorm y
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
      _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * supNorm x + b * supNorm y :=
          add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  exact max_le (hc 0) (hc 1)

theorem openSquare_zero (r : ℝ) : openSquare 0 r = {x | supNorm x < r} := by
  ext x; simp [openSquare, supDist]

theorem closedSquare_zero (r : ℝ) : closedSquare 0 r = {x | supNorm x ≤ r} := by
  ext x; simp [closedSquare, supDist]

/-- The open square about the origin is convex. -/
theorem convex_openSquare (r : ℝ) : Convex ℝ (openSquare 0 r) := by
  rw [openSquare_zero]
  simpa using convexOn_supNorm.convex_lt r

/-- The open square about the origin is open. -/
theorem isOpen_openSquare (r : ℝ) : IsOpen (openSquare 0 r) := by
  rw [openSquare_zero]
  exact isOpen_lt continuous_supNorm continuous_const

/-- The closed square about the origin is closed. -/
theorem isClosed_closedSquare (r : ℝ) : IsClosed (closedSquare 0 r) := by
  rw [closedSquare_zero]
  exact isClosed_le continuous_supNorm continuous_const

/-- The complement of the model curve is the open square together with the outside of the
closed square. -/
theorem compl_modelCurve : modelCurveᶜ = openSquare 0 1 ∪ (closedSquare 0 1)ᶜ := by
  rw [openSquare_zero, closedSquare_zero]
  ext x
  simp only [modelCurve, mem_compl_iff, mem_setOf_eq, mem_union, not_le]
  exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩

end Square

end AVD
