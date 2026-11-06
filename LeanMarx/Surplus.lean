import LeanMarx.Price

set_option linter.unusedSectionVars false

/-!
# Surplus value in the production table

Unpaid labour is defined from the table, not from a price markup.  With a
real wage bundle `b` (goods per unit of labour), the value of labour power is
`v·b`, so employment `L` pays for `(v·b) L` of value and leaves

`S = L (1 − v·b)`

as surplus value.  Under cost prices this surplus is not a price residual
(`ProductionTable.costPrice_netOutput` and
`ProductionTable.costPrice_wage_value_of_labour_power` show the price of net
output is exactly the wage bill), so profit is a claim on `S` distributed
through the parameters of `LeanMarx.Distribution`.
-/

namespace LeanMarx

open Matrix

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]

/-- Value of labour power: labour embodied in the real wage bundle `b` per
unit of labour. -/
noncomputable def valueOfLabourPower (v b : ι → ℝ) : ℝ := v ⬝ᵥ b

namespace ProductionTable

variable (T : ProductionTable ι j)

/-- Surplus value: employment less the labour embodied in the wage goods paid
for it. -/
noncomputable def surplusValue (v b : ι → ℝ) (x : j → ℝ) : ℝ :=
  T.employment x - valueOfLabourPower v b * T.employment x

/-- Wage goods in labour units: variable capital. -/
noncomputable def wageGoodsValue (v b : ι → ℝ) (x : j → ℝ) : ℝ :=
  valueOfLabourPower v b * T.employment x

theorem surplusValue_eq_wageGoods (v b : ι → ℝ) (x : j → ℝ) :
    T.surplusValue v b x = T.employment x - T.wageGoodsValue v b x := rfl

theorem surplusValue_eq (v b : ι → ℝ) (x : j → ℝ) :
    T.surplusValue v b x = (1 - valueOfLabourPower v b) * T.employment x := by
  unfold surplusValue
  ring

/-- Surplus value is positive exactly when the value of labour power is below
one, for positive employment. -/
theorem surplusValue_pos_iff {v b : ι → ℝ} {x : j → ℝ}
    (hL : 0 < T.employment x) :
    0 < T.surplusValue v b x ↔ valueOfLabourPower v b < 1 := by
  rw [T.surplusValue_eq]
  constructor <;> intro h <;> nlinarith

/-- Surplus value is negative for a wage above the value of labour power. -/
theorem surplusValue_neg_iff {v b : ι → ℝ} {x : j → ℝ}
    (hL : 0 < T.employment x) :
    T.surplusValue v b x < 0 ↔ 1 < valueOfLabourPower v b := by
  rw [T.surplusValue_eq]
  constructor <;> intro h <;> nlinarith

end ProductionTable

end LeanMarx
