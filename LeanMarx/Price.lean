import LeanMarx.Basic

/-!
# Sraffa price systems and the class split of net output

Prices of production solve

`p = (1 + r) (p A + w l)`,

where `r` is the uniform profit rate on capital advanced and `w` the money
wage per unit of labour. Dotting against the gross output vector `x` turns
this into the aggregate statement that the price of net output is split
between the wage bill and profit, and identifies the profit with the profit
rate times capital advanced (materials plus wages).

The **wage share** of net output is then an explicit function of the profit
rate and the price-value composition of capital, which is the aggregate
prediction of how income is divided between the two classes.
-/

namespace LeanMarx

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Economy

variable (E : Economy ι)
variable {p : ι → ℝ} {r w : ℝ}

/-- A Sraffa price system: prices equal material costs plus the wage bill,
marked up by the uniform profit rate on capital advanced. -/
def IsPriceSystem (p : ι → ℝ) (r w : ℝ) : Prop :=
  p = (1 + r) • (p ᵥ* E.A + w • E.l)

/-- **Zero profit: prices are labour values.** With no profit markup the
price system has the single solution `p = w v` at *any* composition of
capital, so in that case prices always stand in a labour correspondence. -/
theorem price_value_of_zero_profit (h : E.Productive) {p : ι → ℝ} {w : ℝ}
    (hp : E.IsPriceSystem p 0 w) : p = w • E.value := by
  rw [IsPriceSystem, add_zero, one_smul] at hp
  have h1 : p ᵥ* E.leontief = w • E.l := by
    rw [leontief, vecMul_sub, vecMul_one]
    nth_rewrite 1 [hp]
    rw [add_sub_cancel_left]
  calc p = (p ᵥ* E.leontief) ᵥ* E.leontiefInv := by
        rw [leontiefInv, vecMul_vecMul,
          Matrix.mul_nonsing_inv (A := E.leontief) (show IsUnit E.leontief.det from h),
          vecMul_one]
    _ = (w • E.l) ᵥ* E.leontiefInv := by rw [h1]
    _ = w • E.value := by rw [value, smul_vecMul]

/-- Value of the material inputs consumed by gross output `x`. -/
def capitalAdvanced (p : ι → ℝ) (x : ι → ℝ) : ℝ := p ⬝ᵥ (E.A *ᵥ x)

/-- The wage bill for gross output `x`. -/
def wageBill (w : ℝ) (x : ι → ℝ) : ℝ := w * E.employment x

/-- Aggregate profit: net output at prices minus the wage bill. -/
def profit (p : ι → ℝ) (w : ℝ) (x : ι → ℝ) : ℝ :=
  p ⬝ᵥ E.netOutput x - E.wageBill w x

/-- **Net output at prices: profit plus the wage bill.** The price of net
output is `r (C + Z) + Z` where `C` is material costs and `Z` the wage bill,
because the wage is advanced as capital and marked up with the rest. -/
theorem price_netOutput (h : E.IsPriceSystem p r w) (x : ι → ℝ) :
    p ⬝ᵥ E.netOutput x
      = r * E.capitalAdvanced p x + (1 + r) * E.wageBill w x := by
  have hx : p ⬝ᵥ x = p ⬝ᵥ E.netOutput x + p ⬝ᵥ (E.A *ᵥ x) := by
    rw [netOutput, ← dotProduct_add, ← Matrix.add_mulVec,
      show E.leontief + E.A = 1 by rw [leontief, sub_add_cancel], Matrix.one_mulVec]
  have hp : p ⬝ᵥ x = (1 + r) * (p ⬝ᵥ (E.A *ᵥ x) + w * E.employment x) := by
    have := congrArg (fun v => v ⬝ᵥ x) h
    simpa [IsPriceSystem, smul_dotProduct, add_dotProduct, dotProduct_smul,
      ← dotProduct_mulVec, employment, mul_add, mul_assoc] using this
  unfold capitalAdvanced wageBill
  linarith

/-- **Profit is the profit rate on capital advanced.** Total profit equals
`r` times the sum of material costs and the wage bill. -/
theorem profit_eq (h : E.IsPriceSystem p r w) (x : ι → ℝ) :
    E.profit p w x = r * (E.capitalAdvanced p x + E.wageBill w x) := by
  unfold profit
  have := E.price_netOutput h x
  linarith

/-- Profit is positive exactly when the profit rate is, provided capital
advanced plus the wage bill is positive. -/
theorem profit_pos_iff (h : E.IsPriceSystem p r w) (x : ι → ℝ)
    (hK : 0 < E.capitalAdvanced p x + E.wageBill w x) :
    0 < E.profit p w x ↔ 0 < r := by
  rw [E.profit_eq h x, mul_pos_iff_of_pos_right hK]

/-- Capital intensity in price terms: material costs per unit of wage bill. -/
noncomputable def capitalIntensity (p : ι → ℝ) (w : ℝ) (x : ι → ℝ) : ℝ :=
  E.capitalAdvanced p x / E.wageBill w x

/-- The wage share of net output. -/
noncomputable def wageShare (p : ι → ℝ) (w : ℝ) (x : ι → ℝ) : ℝ :=
  E.wageBill w x / (E.wageBill w x + E.profit p w x)

/-- **Class distribution.** Under a price system the wage share is
`1 / (1 + r (1 + c))`, where `c` is the price-value composition of capital
(material costs per unit of wage bill). Since `r` and `c` are the only
determinants, the division of income between the classes is fixed by the
profit rate and capital intensity. -/
theorem wageShare_eq (h : E.IsPriceSystem p r w) (x : ι → ℝ)
    (hZ : E.wageBill w x ≠ 0) :
    E.wageShare p w x = 1 / (1 + r * (1 + E.capitalIntensity p w x)) := by
  have hp := E.profit_eq h x
  unfold wageShare
  rw [hp]
  rw [capitalIntensity]
  field_simp
  ring

/-- The wage share falls strictly as the profit rate rises, for any positive
capital intensity. This is the distributional prediction: a higher profit
rate redistributes net output towards capital. -/
theorem wageShare_strictAnti {r₁ r₂ c : ℝ} (hc : 0 < c) (hr : 0 ≤ r₁)
    (hlt : r₁ < r₂) :
    1 / (1 + r₂ * (1 + c)) < 1 / (1 + r₁ * (1 + c)) := by
  have h₁ : 0 < 1 + r₁ * (1 + c) := by nlinarith
  have h₂ : 0 < 1 + r₂ * (1 + c) := by nlinarith
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

end Economy

end LeanMarx
