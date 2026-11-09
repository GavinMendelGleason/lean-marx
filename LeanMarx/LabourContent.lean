import LeanMarx.ValueDetermination

set_option linter.unusedSectionVars false

/-!
# Labour content under dispersed profit rates

Labour values are determined by the production table:

`v (B − A) = l`.

The profit-rate distribution does not enter this equation.  A dispersion of
profit rates changes prices, not values.  This module records that, and the
converse identification result: if prices, the input matrix, the wage and the
**dispersed** profit-rate vector are known, the direct labour input of each
activity is recoverable, and hence the labour value follows from the table.

The distinction is:

* **determination** — values are fixed by the technique, independently of
  prices and profit rates;
* **identification** — values can be recovered from prices plus the production
  coefficients and the rate vector, but not from prices alone.
-/

namespace LeanMarx

open Matrix

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]

namespace ProductionTable

variable (T : ProductionTable ι j)

/-- A price system with a **dispersed** profit-rate vector: activity `j`'s
output price equals `(1 + r j)` times its input cost. -/
def IsSectoralPrice (p : ι → ℝ) (w : ℝ) (r : j → ℝ) : Prop :=
  ∀ j, p ⬝ᵥ (T.B *ᵥ Pi.single j 1)
    = (1 + r j) * (p ⬝ᵥ (T.A *ᵥ Pi.single j 1) + w * T.l j)

/-- **Recovering direct labour input under dispersed rates.** Given prices,
the profit-rate vector, the input matrix and the wage, each activity's labour
input is determined. -/
theorem recover_labourInput {p : ι → ℝ} {w : ℝ} {r : j → ℝ}
    (hp : T.IsSectoralPrice p w r) (j : j) (hw : w ≠ 0) (hr : 1 + r j ≠ 0) :
    T.l j = (p ⬝ᵥ (T.B *ᵥ Pi.single j 1) / (1 + r j)
      - p ⬝ᵥ (T.A *ᵥ Pi.single j 1)) / w := by
  have h := hp j
  field_simp [hw, hr]
  linarith

/-- **Labour values do not depend on prices or on the distribution of profit
rates.** The predicate is a property of the table alone. -/
theorem isLabourValue_independent_of_prices {v : ι → ℝ} (hv : T.IsLabourValue v)
    (p : ι → ℝ) (w : ℝ) (r : j → ℝ) : T.IsLabourValue v := hv

/-- **The unique labour value exists independently of the price system.** -/
theorem existsUnique_labourValue_independent (h : T.DeterminesValues)
    (p : ι → ℝ) (w : ℝ) (r : j → ℝ) :
    ∃! v : ι → ℝ, T.IsLabourValue v :=
  T.existsUnique_labourValue h

end ProductionTable

end LeanMarx
