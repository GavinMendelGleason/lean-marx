import LeanMarx.Shares

set_option linter.unusedSectionVars false

/-!
# Recovering the average profit rate

The average profit rate is the average price difference between total inputs
and product sale, divided by total input cost:

`averageProfitRate = (revenue − cost) / cost`,
`cost = p · (A x) + w · (l · x)`,
`revenue = p · (B x)`.

Consequences:

* cost prices leave no surplus: `averageProfitRate = 0` when `p (B − A) = w l`;
* a price system with a uniform profit rate `r`, `p B = (1+r)(p A + w l)`,
  returns exactly `r` from the price difference;
* at the market prices of this model the profit numerator is exactly the rent,
  so the average rate is rent over total input cost — not the markup `μ` and
  not the rent share of net output.
-/

namespace LeanMarx

open Matrix

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]

namespace ProductionTable

variable (T : ProductionTable ι j)

/-- Total input cost at prices `p` and wage `w`: materials plus wages. -/
noncomputable def totalInputCost (p : ι → ℝ) (w : ℝ) (x : j → ℝ) : ℝ :=
  p ⬝ᵥ (T.A *ᵥ x) + w * (T.l ⬝ᵥ x)

/-- Sale value of the output vector. -/
noncomputable def totalRevenue (p : ι → ℝ) (x : j → ℝ) : ℝ :=
  p ⬝ᵥ (T.B *ᵥ x)

/-- The average profit rate: profit over total input cost. -/
noncomputable def averageProfitRate (p : ι → ℝ) (w : ℝ) (x : j → ℝ) : ℝ :=
  (T.totalRevenue p x - T.totalInputCost p w x) / T.totalInputCost p w x

/-- A price system with a uniform profit rate `r`:
`p B = (1 + r)(p A + w l)`. -/
def IsProfitRatePrice (p : ι → ℝ) (r w : ℝ) : Prop :=
  p ᵥ* T.B = (1 + r) • (p ᵥ* T.A + w • T.l)

/-- Profit is revenue less cost, written through net output and employment. -/
theorem totalRevenue_sub_totalInputCost (p : ι → ℝ) (w : ℝ) (x : j → ℝ) :
    T.totalRevenue p x - T.totalInputCost p w x
      = p ⬝ᵥ (T.netOutput x) - w * T.employment x := by
  unfold totalRevenue totalInputCost netOutput employment
  rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec]
  rw [netOp, vecMul_sub, sub_dotProduct]
  ring

/-- The profit rate written against net output. -/
theorem averageProfitRate_eq (p : ι → ℝ) (w : ℝ) (x : j → ℝ) :
    T.averageProfitRate p w x
      = (p ⬝ᵥ (T.netOutput x) - w * T.employment x)
        / T.totalInputCost p w x := by
  unfold averageProfitRate
  rw [totalRevenue_sub_totalInputCost]

/-- **Cost prices leave no surplus.** -/
theorem averageProfitRate_costPrice {p : ι → ℝ} {w : ℝ} (hp : T.IsCostPrice p w)
    {x : j → ℝ} (hcost : T.totalInputCost p w x ≠ 0) :
    T.averageProfitRate p w x = 0 := by
  rw [averageProfitRate_eq]
  have h : p ⬝ᵥ (T.netOutput x) - w * T.employment x = 0 := by
    rw [T.costPrice_netOutput hp x, sub_self]
  rw [h, zero_div]

/-- **Recovering a uniform profit rate.** If prices satisfy the Sraffa
condition `p B = (1+r)(p A + w l)`, the price difference divided by total
input cost is exactly `r`. -/
theorem averageProfitRate_eq_of_profitRatePrice {p : ι → ℝ} {r w : ℝ}
    (hp : T.IsProfitRatePrice p r w) {x : j → ℝ}
    (hcost : T.totalInputCost p w x ≠ 0) :
    T.averageProfitRate p w x = r := by
  have hrev : T.totalRevenue p x = (1 + r) * T.totalInputCost p w x := by
    unfold totalRevenue totalInputCost
    rw [dotProduct_mulVec, dotProduct_mulVec, hp, smul_dotProduct,
      add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  rw [averageProfitRate, hrev]
  field_simp [hcost]
  ring

end ProductionTable

/-! ## The market-price case: profit is rent -/

namespace ProducerTable

variable {φ : Type*} [Fintype φ] [DecidableEq φ]
variable (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ} {μ : ι → ℝ} {x : φ → ℝ}

/-- **The profit numerator is the rent.** At the model's market prices the
sale value less total input cost equals the rent on the net output. -/
theorem marketPrice_profit_eq_rent (hx : T.toTable.IsLabourValue v) :
    T.toTable.totalRevenue (T.marketPrice v w μ) x
      - T.toTable.totalInputCost (T.marketPrice v w μ) w x
      = T.aggregateRent v w μ (T.toTable.netOutput x) := by
  rw [T.toTable.totalRevenue_sub_totalInputCost, T.aggregateRent_eq_gap_dot]
  have hp : T.marketPrice v w μ = w • v + priceGap (T.marketPrice v w μ) v w := by
    ext c
    simp [priceGap]
  have hv : v ⬝ᵥ T.toTable.netOutput x = T.toTable.employment x :=
    T.toTable.value_netOutput hx x
  conv_lhs => rw [hp]
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hv]
  ring

/-- The average profit rate at market prices is rent over total input cost. -/
theorem averageProfitRate_marketPrice_eq_rent_div (hx : T.toTable.IsLabourValue v) :
    T.toTable.averageProfitRate (T.marketPrice v w μ) w x
      = T.aggregateRent v w μ (T.toTable.netOutput x)
        / T.toTable.totalInputCost (T.marketPrice v w μ) w x := by
  unfold ProductionTable.averageProfitRate
  rw [marketPrice_profit_eq_rent T hx]

end ProducerTable

end LeanMarx
