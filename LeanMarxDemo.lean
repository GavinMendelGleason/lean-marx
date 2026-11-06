import LeanMarx

set_option linter.unusedSimpArgs false

/-!
# Worked production tables

* `singleT` — the classical single-product table (`B = 1`): values exist
  uniquely and are `(4,4)`; cost prices are `w · (4,4)`.
* `jointOkT` — genuine joint production with an invertible net-output
  operator: values are still unique.
* `jointT` — joint production with a rank-one net-output operator: the table
  does **not** determine values.  Two distinct value vectors exist for one
  labour input, and none exists for another.
-/

namespace LeanMarx

open Matrix
open ProductionTable

/-! ## Single-product table (the old model as the case `B = 1`) -/

noncomputable def singleA : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 1/4; 1/4, 1/2]

/-- Two sectors, one hour per unit of output, make matrix the identity. -/
noncomputable def singleT : ProductionTable (Fin 2) (Fin 2) :=
  { A := singleA, B := 1, l := ![1, 1] }

theorem singleT_netOp : singleT.netOp = 1 - singleA := by
  ext i k
  simp [singleT, netOp]

theorem singleT_det : singleT.netOp.det = 3 / 16 := by
  rw [singleT_netOp, Matrix.det_fin_two]
  simp [singleA]
  norm_num

/-- The inverse of `1 − A`. -/
noncomputable def singleInv : Matrix (Fin 2) (Fin 2) ℝ := !![8 / 3, 4 / 3; 4 / 3, 8 / 3]

theorem singleInv_left : singleInv * singleT.netOp = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [singleInv, singleT, netOp, singleA, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

theorem singleInv_right : singleT.netOp * singleInv = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [singleInv, singleT, netOp, singleA, Matrix.mul_apply, Fin.sum_univ_two] <;>
    norm_num

/-- The table determines labour values: `1 − A` is invertible. -/
theorem singleT_determines : singleT.DeterminesValues :=
  ⟨⟨singleInv, singleInv_left⟩, ⟨singleInv, singleInv_right⟩⟩

/-- Labour values are `(4,4)`: four hours embodied in each commodity. -/
theorem singleT_labourValue : singleT.labourValue singleInv = ![4, 4] := by
  unfold ProductionTable.labourValue
  ext i
  fin_cases i <;>
    simp [singleT, singleInv, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    norm_num

theorem singleT_value : singleT.IsLabourValue ![4, 4] := by
  have h := singleT.labourValue_isLabourValue singleInv_left
  rwa [singleT_labourValue] at h

/-- **Cost prices are proportional to labour values.** Every cost price is
the wage rate times `(4,4)`. -/
theorem singleT_correspondence {p : Fin 2 → ℝ} {w : ℝ}
    (hp : singleT.IsCostPrice p w) : p = w • ![4, 4] :=
  singleT.costPrice_eq_smul_labourValue singleT_determines.2 hp singleT_value

theorem singleT_costPrice_concretely : singleT.IsCostPrice ![4, 4] 1 := by
  simpa using singleT.costPrice_of_labourValue singleT_value 1

/-! ## Joint production, invertible net output -/

noncomputable def jointOkA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
noncomputable def jointOkB : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 0, 2]

/-- Process 0 makes two units of commodity 0 and one of commodity 1;
process 1 makes two units of commodity 1. -/
noncomputable def jointOkT : ProductionTable (Fin 2) (Fin 2) :=
  { A := jointOkA, B := jointOkB, l := ![1, 1] }

theorem jointOkT_netOp : jointOkT.netOp = !![1, 1; 0, 1] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [jointOkT, netOp, jointOkA, jointOkB]
  all_goals norm_num

noncomputable def jointOkInv : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 1]

theorem jointOkInv_left : jointOkInv * jointOkT.netOp = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [jointOkInv, jointOkT_netOp, Matrix.mul_apply, Fin.sum_univ_two]

theorem jointOkInv_right : jointOkT.netOp * jointOkInv = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [jointOkInv, jointOkT_netOp, Matrix.mul_apply, Fin.sum_univ_two]

/-- Joint production is not degenerate: this table determines values. -/
theorem jointOkT_determines : jointOkT.DeterminesValues :=
  ⟨⟨jointOkInv, jointOkInv_left⟩, ⟨jointOkInv, jointOkInv_right⟩⟩

theorem jointOkT_value : jointOkT.IsLabourValue ![1, 0] := by
  unfold ProductionTable.IsLabourValue
  rw [jointOkT_netOp]
  ext i
  fin_cases i <;> simp [jointOkT, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- ... and the value is unique. -/
theorem jointOkT_unique_value :
    ∃! v : Fin 2 → ℝ, jointOkT.IsLabourValue v :=
  jointOkT.existsUnique_labourValue jointOkT_determines

/-! ## Joint production, rank-one net output: values fail -/

noncomputable def jointA : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
noncomputable def jointB : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

/-- Both processes have the same net output `(1,1)` per unit of activity. -/
noncomputable def jointT : ProductionTable (Fin 2) (Fin 2) :=
  { A := jointA, B := jointB, l := ![1, 1] }

theorem jointT_netOp : jointT.netOp = !![1, 1; 1, 1] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [jointT, netOp, jointA, jointB]
  all_goals norm_num

/-- Two distinct labour-value vectors for the same table. -/
theorem jointT_values_not_unique :
    ∃ v₁ v₂ : Fin 2 → ℝ, v₁ ≠ v₂ ∧
      jointT.IsLabourValue v₁ ∧ jointT.IsLabourValue v₂ := by
  refine ⟨![1, 0], ![0, 1], ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · unfold ProductionTable.IsLabourValue
    rw [jointT_netOp]
    ext i
    fin_cases i <;> simp [jointT, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · unfold ProductionTable.IsLabourValue
    rw [jointT_netOp]
    ext i
    fin_cases i <;> simp [jointT, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- For labour input `(1,0)` there is **no** labour value at all. -/
theorem jointT_no_value_for :
    ¬ ∃ v : Fin 2 → ℝ, v ᵥ* jointT.netOp = ![1, 0] := by
  rintro ⟨v, hv⟩
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [jointT_netOp, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
  linarith

/-- `B − A` has no left inverse, so not every labour input has a value. -/
theorem jointT_valuesExist_false : ¬ jointT.ValuesExist := by
  rintro ⟨C, hC⟩
  have hcol : (C * jointT.netOp) 0 0 = (C * jointT.netOp) 0 1 := by
    simp [jointT_netOp, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hC] at hcol
  simp at hcol

/-- `B − A` has no right inverse, so values are not unique. -/
theorem jointT_valuesUnique_false : ¬ jointT.ValuesUnique := by
  rintro ⟨D, hD⟩
  have hrow : (jointT.netOp * D) 0 0 = (jointT.netOp * D) 1 0 := by
    simp [jointT_netOp, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hD] at hrow
  simp at hrow

end LeanMarx
