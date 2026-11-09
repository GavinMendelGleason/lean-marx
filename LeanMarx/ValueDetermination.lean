import LeanMarx.RentTheory
import LeanMarx.Demand

set_option linter.unusedSectionVars false

/-!
# Labour values versus commodity substitution

Under cost pricing and a single-product table that determines labour values,
prices are exactly proportional to labour values:

`p = w • v`,   hence   `p i / p j = v i / v j`.

This is the strongest "labour values determine prices" statement the model
supports: the labour-value vector is a sufficient statistic for relative
prices.  A commodity substitution changes the input matrix `A`, hence changes
`v` and `p` together; the correspondence is preserved for the new table.  So
substitution is not an *alternative* determinant of price — it is the basis
from which the labour values are computed.

What breaks the determination is distribution and market structure, not
substitution:

`p = w • v + gap`,   `gap = priceGap p v w = p − w • v`.

At the model's market prices the gap is exactly the rent wedge.  Prices are
proportional to labour values iff the gap is zero; a monopoly, a markup, a
rent, joint production or a non-unique value vector all make the gap nonzero
or the value vector unavailable.

Demand substitution is a separate channel: in the cost-price model demand
determines quantities, not prices.  With markups, demand elasticity feeds into
the markup and hence into the gap, not into the labour values.
-/

namespace LeanMarx

open Matrix

variable {ι j φ : Type*} [Fintype ι] [Fintype j] [Fintype φ]
  [DecidableEq ι] [DecidableEq j] [DecidableEq φ]

namespace ProductionTable

variable (T : ProductionTable ι j) {p : ι → ℝ} {w : ℝ} {v : ι → ℝ}

/-- **Labour values determine relative prices.** Under cost pricing and unique
values, the price ratio is the labour-value ratio. -/
theorem price_ratio_eq_value_ratio (hU : T.ValuesUnique) (hp : T.IsCostPrice p w)
    (hv : T.IsLabourValue v) (hw : w ≠ 0) {i j : ι} (hj : v j ≠ 0) :
    p i / p j = v i / v j := by
  rw [T.costPrice_eq_smul_labourValue hU hp hv]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hw, hj]

/-- **Unit wage: price equals labour value.** -/
theorem price_eq_value_of_unit_wage (hU : T.ValuesUnique) (hp : T.IsCostPrice p 1)
    (hv : T.IsLabourValue v) : p = v := by
  simpa using T.costPrice_eq_smul_labourValue hU hp hv

end ProductionTable

/-- The price–labour decomposition: price is the wage-weighted labour value
plus a gap. -/
theorem price_eq_labour_add_gap (p v : ι → ℝ) (w : ℝ) :
    p = w • v + priceGap p v w := by
  ext c
  simp [priceGap]

/-- **Zero gap iff prices are proportional to labour values.** -/
theorem priceGap_eq_zero_iff {p v : ι → ℝ} {w : ℝ} :
    priceGap p v w = 0 ↔ p = w • v := by
  constructor
  · intro h
    rw [price_eq_labour_add_gap p v w, h, add_zero]
  · intro h
    rw [h]
    ext c
    simp [priceGap]

/-- **The market-price gap is the rent wedge.** A specific commodity with a
monopoly wedge departs from its labour value by exactly that wedge. -/
theorem marketPrice_gap_eq (T : ProducerTable ι φ) (v : ι → ℝ) (w : ℝ)
    (μ : ι → ℝ) :
    priceGap (T.marketPrice v w μ) v w
      = fun c => T.rent v w μ (fun _ => 1) c := by
  ext c
  simp [priceGap, ProducerTable.marketPrice, ProducerTable.rent]

/-- With no monopoly the gap vanishes: prices are labour values. -/
theorem marketPrice_gap_zero_of_no_monopoly (T : ProducerTable ι φ) (v : ι → ℝ)
    (w : ℝ) (μ : ι → ℝ) (h : ∀ c, ¬ T.IsMonopoly c) :
    priceGap (T.marketPrice v w μ) v w = 0 := by
  rw [marketPrice_gap_eq]
  ext c
  exact T.rent_of_not_monopoly (h c)

end LeanMarx
