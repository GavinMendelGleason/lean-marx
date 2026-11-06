import LeanMarx.Basic

set_option linter.unusedSectionVars false

/-!
# Dual cost prices of the production table

Prices are the dual of the table, not an added markup theory: a price vector
`p` is a **cost price** at wage `w` when the price of net output covers the
wage bill,

`p (B − A) = w l`.

There is no uniform profit rate and no Sraffa equation.  Consequences:

* prices exist exactly when labour values do — it is the same linear system,
  scaled by `w`;
* when the table determines labour values, every cost price is the wage rate
  times the labour-value vector, so the price–value correspondence is a
  theorem rather than a condition;
* with cost prices and a wage equal to the price of the real wage bundle, the
  value of labour power is exactly one: cost pricing leaves no surplus.  That
  is why profit is carried by the distributional parameters of
  `LeanMarx.Distribution` and not by prices.
-/

namespace LeanMarx

open Matrix

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]

namespace ProductionTable

variable (T : ProductionTable ι j)
variable {p : ι → ℝ} {w : ℝ}

/-- A cost price system: the price of net output equals the wage bill,
`p (B − A) = w l`. -/
def IsCostPrice (p : ι → ℝ) (w : ℝ) : Prop := p ᵥ* T.netOp = w • T.l

/-- Every labour value gives a cost price by scaling with the wage. -/
theorem costPrice_of_labourValue {v : ι → ℝ} (hv : T.IsLabourValue v) (w : ℝ) :
    T.IsCostPrice (w • v) w := by
  unfold IsCostPrice
  rw [smul_vecMul, hv]

/-- **Price–value correspondence.** When the table determines labour values,
every cost price vector is the wage rate times the labour-value vector. -/
theorem costPrice_eq_smul_labourValue (hU : T.ValuesUnique) {v : ι → ℝ}
    (hp : T.IsCostPrice p w) (hv : T.IsLabourValue v) : p = w • v := by
  obtain ⟨D, hD⟩ := hU
  have h0 : (p - w • v) ᵥ* T.netOp = 0 := by
    rw [sub_vecMul, hp, smul_vecMul, hv, sub_self]
  have hEq : p - w • v = (p - w • v) ᵥ* (T.netOp * D) := by
    rw [hD, vecMul_one]
  rw [← vecMul_vecMul, h0, zero_vecMul] at hEq
  exact sub_eq_zero.mp hEq

/-- **Prices and labour values stand or fall together.** A cost price exists
exactly when a labour value does, since it is the same linear system scaled by
the wage. -/
theorem costPrice_exists_iff (hw : w ≠ 0) :
    (∃ p : ι → ℝ, T.IsCostPrice p w) ↔ (∃ v : ι → ℝ, T.IsLabourValue v) := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨w⁻¹ • p, ?_⟩
    unfold IsLabourValue
    rw [smul_vecMul, hp, smul_smul, inv_mul_cancel₀ hw, one_smul]
  · rintro ⟨v, hv⟩
    exact ⟨w • v, T.costPrice_of_labourValue hv w⟩

/-- The value of net output at cost prices is exactly the wage bill: there is
no price-theoretic residual out of which profit could be paid. -/
theorem costPrice_netOutput (hp : T.IsCostPrice p w) (x : j → ℝ) :
    p ⬝ᵥ T.netOutput x = w * T.employment x := by
  rw [netOutput, employment, dotProduct_mulVec, hp, smul_dotProduct, smul_eq_mul]

/-- **Cost prices leave no surplus.** If the wage is the price of a real wage
bundle `b`, then under cost prices the value of labour power is exactly one:
workers receive the full value of what they produce. -/
theorem costPrice_wage_value_of_labour_power (hU : T.ValuesUnique)
    {v : ι → ℝ} (hp : T.IsCostPrice p w) (hv : T.IsLabourValue v) (hw : w ≠ 0)
    {b : ι → ℝ} (hb : w = p ⬝ᵥ b) : v ⬝ᵥ b = 1 := by
  have hpv := T.costPrice_eq_smul_labourValue hU hp hv
  rw [hpv, smul_dotProduct] at hb
  have hb' : w = w * (v ⬝ᵥ b) := by simpa [smul_eq_mul] using hb
  have hcancel : w * 1 = w * (v ⬝ᵥ b) := by rw [mul_one]; exact hb'
  exact (mul_left_cancel₀ hw hcancel).symm

end ProductionTable

end LeanMarx
