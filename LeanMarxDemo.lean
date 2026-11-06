import LeanMarx

set_option linter.unusedSimpArgs false

/-!
# Worked examples

Two two-sector economies exercise the labour-correspondence criterion of
`LeanMarx.Correspondence`.

* `equalComposition` has equal organic composition: its direct labour vector
  is a left eigenvector of the input matrix, so a price vector proportional
  to labour values exists (and the reverse direction of the criterion
  produces one).
* `unequalComposition` does not, so **no** price system with a nonzero
  profit rate can be proportional to labour values.
-/

namespace LeanMarx

open Matrix

/-! ## Equal organic composition -/

/-- Symmetric input matrix with equal row sums. -/
noncomputable def equalA : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/4; 1/4, 1/2]

/-- Two sectors, one hour per unit of output in each. -/
noncomputable def equalE : Economy (Fin 2) := { A := equalA, l := ![1, 1] }

theorem equalE_productive : equalE.Productive := by
  rw [Economy.Productive, Economy.leontief, isUnit_iff_ne_zero, Matrix.det_fin_two]
  simp [equalE, equalA]
  norm_num

/-- The direct labour vector is a left eigenvector with eigenvalue `3/4`, so
all sectors have the same organic composition of capital. -/
theorem equalE_leftEigen : equalE.l ᵥ* equalE.A = (3 / 4 : ℝ) • equalE.l := by
  ext i
  fin_cases i <;>
    simp [equalE, equalA, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- Labour values are proportional to direct labour. -/
theorem equalE_value_proportional :
    Proportional equalE.value equalE.l :=
  (equalE.value_proportional_labour_iff_leftEigen equalE_productive).mpr
    ⟨3 / 4, equalE_leftEigen⟩

/-- Prices `(20, 20)` solve the Sraffa system at profit rate `1/4` and wage
`1`; the price matrix is invertible there. -/
theorem equalE_priceSystem :
    equalE.IsPriceSystem ![20, 20] (1 / 4) 1 := by
  ext i
  fin_cases i <;>
    simp [Economy.IsPriceSystem, equalE, equalA, Matrix.vecMul, dotProduct,
      Matrix.add_apply, Fin.sum_univ_two] <;>
    norm_num

theorem equalE_priceMatrix_invertible :
    IsUnit (equalE.priceMatrix (1 / 4)).det := by
  rw [isUnit_iff_ne_zero, Economy.priceMatrix, Matrix.det_fin_two]
  simp [equalE, equalA]
  norm_num

theorem equalE_value_ne_zero : equalE.value ≠ 0 := by
  intro h0
  have hl : equalE.l = 0 := by
    rw [← equalE.value_leontief equalE_productive, h0, zero_vecMul]
  have : (1 : ℝ) = 0 := by simpa [equalE] using congrFun hl 0
  norm_num at this

/-- Labour values are `(4, 4)`: four hours embodied in each commodity. -/
theorem equalE_value_eq : equalE.value = ![4, 4] := by
  have hinj := Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det equalE.leontief).mpr equalE_productive)
  apply hinj
  change equalE.value ᵥ* equalE.leontief = (![4, 4] : Fin 2 → ℝ) ᵥ* equalE.leontief
  rw [equalE.value_leontief equalE_productive]
  ext i
  fin_cases i <;>
    simp [equalE, equalA, Economy.leontief, vecMul, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- The price vector is exactly five times the value vector. -/
theorem equalE_price_eq_five_value : (![20, 20] : Fin 2 → ℝ) = 5 • equalE.value := by
  rw [equalE_value_eq]
  ext i
  fin_cases i <;> norm_num

/-- **A labour correspondence exists.** Prices are proportional to labour
values at the actual profit rate and wage. -/
theorem equalE_price_proportional_value :
    Proportional ![20, 20] equalE.value :=
  (equalE.price_proportional_value_iff (equalE.value_leontief equalE_productive)
    equalE_value_ne_zero equalE_priceMatrix_invertible equalE_priceSystem
    (by norm_num) (by norm_num) (by norm_num)).mpr equalE_value_proportional

/-! ## Unequal organic composition -/

/-- Upper-triangular input matrix: sector 1 uses sector 1's output only. -/
noncomputable def unequalA : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/2; 0, 1/2]

/-- Only sector 0 is labour-using. -/
noncomputable def unequalE : Economy (Fin 2) := { A := unequalA, l := ![1, 0] }

theorem unequalE_productive : unequalE.Productive := by
  rw [Economy.Productive, Economy.leontief, isUnit_iff_ne_zero, Matrix.det_fin_two]
  simp [unequalE, unequalA]
  norm_num

/-- The direct labour vector is **not** a left eigenvector: the first
coordinate forces eigenvalue `1/2`, which the second coordinate contradicts. -/
theorem unequalE_not_leftEigen :
    ¬ ∃ μ : ℝ, unequalE.l ᵥ* unequalE.A = μ • unequalE.l := by
  rintro ⟨μ, hμ⟩
  have h1 : (unequalE.l ᵥ* unequalE.A) 1 = (μ • unequalE.l) 1 := by rw [hμ]
  simp [unequalE, unequalA, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h1

/-- Labour values are `(2, 2)` here, while direct labour is `(1, 0)`: the two
are not proportional. -/
theorem unequalE_value_eq : unequalE.value = ![2, 2] := by
  have hinj := Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det unequalE.leontief).mpr unequalE_productive)
  apply hinj
  change unequalE.value ᵥ* unequalE.leontief = (![2, 2] : Fin 2 → ℝ) ᵥ* unequalE.leontief
  rw [unequalE.value_leontief unequalE_productive]
  ext i
  fin_cases i <;>
    simp [unequalE, unequalA, Economy.leontief, vecMul, dotProduct, Fin.sum_univ_two] <;>
    norm_num

/-- Hence no price system with nonzero profit rate is proportional to labour
values, whatever the wage. -/
theorem unequalE_no_price_proportional_value
    (p : Fin 2 → ℝ) (r w : ℝ) (hp : unequalE.IsPriceSystem p r w)
    (hM : IsUnit (unequalE.priceMatrix r).det)
    (hr : r ≠ 0) (hw : w ≠ 0) (hr1 : 1 + r ≠ 0) :
    ¬ Proportional p unequalE.value := by
  intro hpc
  have hvl := unequalE.value_leontief unequalE_productive
  have hvne : unequalE.value ≠ 0 := by
    intro h0
    have hl : unequalE.l = 0 := by
      rw [← hvl, h0, zero_vecMul]
    have : (1 : ℝ) = 0 := by simpa [unequalE] using congrFun hl 0
    norm_num at this
  exact unequalE_not_leftEigen
    ((unequalE.value_proportional_labour_iff_leftEigen unequalE_productive).mp
      ((unequalE.price_proportional_value_iff hvl hvne hM hp hr hw hr1).mp hpc))

end LeanMarx
