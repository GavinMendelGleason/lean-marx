import LeanMarx.Surplus

set_option linter.unusedSectionVars false

/-!
# The tendency of the rate of profit to fall

The value rate of profit is

`r = S / (C + V) = (S/V) / (C/V + 1)`.

The determinant is the **value** composition `C/V` — the organic composition
of capital — relative to the rate of surplus value `S/V`.  The physical volume
of means of production per worker is the *technical* composition; it is not
what enters `r`.  A rising physical capital–labour ratio can coexist with a
falling `C/V` if productivity cheapens the means of production.

So the tendency is captured by `C/V` rising relative to `S/V`, not by
"increasing total volume of commodities relative to labour" as such.  The
model gives the condition; it does not yet endogenise the technical change
that makes `C/V` rise, nor the counteracting tendencies (a rising `S/V`, the
cheapening of constant capital).
-/

namespace LeanMarx

open Matrix

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]

namespace ProductionTable

variable (T : ProductionTable ι j) (v b : ι → ℝ) (x : j → ℝ)

/-- The rate of surplus value, `S/V`. -/
noncomputable def rateOfSurplusValue : ℝ :=
  T.surplusValue v b x / T.wageGoodsValue v b x

/-- The organic composition of capital, `C/V`. -/
noncomputable def organicComposition : ℝ :=
  T.constantCapital v x / T.wageGoodsValue v b x

/-- **The profit-rate decomposition.** `r = (S/V) / (C/V + 1)`. -/
theorem valueProfitRate_eq_rate_div (hV : T.wageGoodsValue v b x ≠ 0) :
    T.valueProfitRate v b x
      = T.rateOfSurplusValue v b x / (T.organicComposition v b x + 1) := by
  unfold valueProfitRate rateOfSurplusValue organicComposition
  field_simp [hV]

end ProductionTable

/-! ## The comparative statics of the formula -/

/-- **A higher organic composition lowers the profit rate**, at a fixed
surplus value and variable capital. -/
theorem profitRate_antitone_constant {S V C₁ C₂ : ℝ} (hV : 0 < V) (hS : 0 ≤ S)
    (hC₁ : 0 ≤ C₁) (h : C₁ ≤ C₂) :
    S / (C₂ + V) ≤ S / (C₁ + V) := by
  have h₁ : 0 < C₁ + V := by linarith
  have h₂ : 0 < C₂ + V := by linarith
  rw [div_le_div_iff₀ h₂ h₁]
  nlinarith

/-- **A higher surplus value raises the profit rate**, at a fixed capital
advanced. -/
theorem profitRate_mono_surplus {S₁ S₂ V C : ℝ} (hV : 0 < V) (hC : 0 ≤ C)
    (h : S₁ ≤ S₂) :
    S₁ / (C + V) ≤ S₂ / (C + V) := by
  have hden : 0 < C + V := by linarith
  exact div_le_div_of_nonneg_right h hden.le

/-- **The tendency.** Constant capital rises and surplus value does not rise:
the profit rate falls. -/
theorem profitRate_falls {S₁ S₂ C₁ C₂ V : ℝ} (hV : 0 < V)
    (hC₁ : 0 ≤ C₁) (hC : C₁ ≤ C₂) (hS : S₂ ≤ S₁) (hS₁ : 0 ≤ S₁) :
    S₂ / (C₂ + V) ≤ S₁ / (C₁ + V) := by
  have h₁ : 0 < C₁ + V := by linarith
  have h₂ : 0 < C₂ + V := by linarith
  rw [div_le_div_iff₀ h₂ h₁]
  nlinarith [mul_le_mul_of_nonneg_right hS h₁.le,
    mul_le_mul_of_nonneg_left hC hS₁]

/-- **The keep-pace condition.** With surplus value growing at `gS`, constant
capital at `gC` and variable capital at `gV`, the profit rate does not fall iff

`gS ≥ (C gC + V gV) / (C + V)`.

The required surplus-value growth is the capital-weighted average of the
capital growth rates.  Cheapening of constant capital (a negative contribution
to `gC`) or of wage goods (a negative contribution to `gV`) lowers the
required rate; mechanisation (a positive `gC`) raises it. -/
theorem profitRate_growth_iff {S C V gS gC gV : ℝ} (hS : 0 < S) (hC : 0 < C)
    (hV : 0 < V) (hgC : -1 < gC) (hgV : -1 < gV) :
    S * (1 + gS) / (C * (1 + gC) + V * (1 + gV)) ≥ S / (C + V)
      ↔ gS ≥ (C * gC + V * gV) / (C + V) := by
  have hden : 0 < C + V := by linarith
  have hC' : 0 < C * (1 + gC) := mul_pos hC (by linarith)
  have hV' : 0 < V * (1 + gV) := mul_pos hV (by linarith)
  have hden' : 0 < C * (1 + gC) + V * (1 + gV) := by linarith
  rw [ge_iff_le, div_le_div_iff₀ hden hden']
  constructor
  · intro h
    rw [ge_iff_le, div_le_iff₀ hden]
    nlinarith
  · intro h
    rw [ge_iff_le, div_le_iff₀ hden] at h
    nlinarith

end LeanMarx
