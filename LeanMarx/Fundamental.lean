import LeanMarx.Correspondence
import LeanMarx.Distribution

/-!
# Profit versus surplus value

Under the labour correspondence `p = k v` of `LeanMarx.Correspondence`, the
money profit of a gross output `x` is `k` times the surplus value extracted
in producing it. The rate of profit is therefore the value rate of profit,
independent of the price–value multiplier `k`.

This is where the two halves of the development meet: the correspondence is
what makes the price-based class distribution of `LeanMarx.Distribution`
coincide with the value-based exploitation accounting.
-/

namespace LeanMarx

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Economy

variable (E : Economy ι)

/-- Value of labour power: the labour embodied in the real wage bundle `b`
per unit of labour. -/
noncomputable def valueOfLabourPower (b : ι → ℝ) : ℝ := E.value ⬝ᵥ b

/-- Surplus value: total employment minus the labour embodied in the wage
goods paid for it. -/
noncomputable def surplusValue (b : ι → ℝ) (x : ι → ℝ) : ℝ :=
  E.employment x - E.valueOfLabourPower b * E.employment x

/-- Constant capital: labour embodied in the material inputs consumed. -/
noncomputable def constantCapital (x : ι → ℝ) : ℝ := E.value ⬝ᵥ (E.A *ᵥ x)

/-- Variable capital: labour embodied in the wage goods advanced. -/
noncomputable def variableCapital (b : ι → ℝ) (x : ι → ℝ) : ℝ :=
  E.valueOfLabourPower b * E.employment x

/-- The value rate of profit: surplus value over constant and variable
capital. -/
noncomputable def valueProfitRate (b : ι → ℝ) (x : ι → ℝ) : ℝ :=
  E.surplusValue b x / (E.constantCapital x + E.variableCapital b x)

/-- **Profit is the price–value multiplier times surplus value.** When prices
are proportional to labour values and the money wage is the price of the wage
bundle, profit and surplus value agree up to the same factor `k`. -/
theorem profit_eq_surplusValue (h : E.Productive) {p : ι → ℝ} {k w : ℝ}
    {b : ι → ℝ} (hpv : p = k • E.value) (hw : w = p ⬝ᵥ b) (x : ι → ℝ) :
    E.profit p w x = k * E.surplusValue b x := by
  unfold profit surplusValue valueOfLabourPower wageBill
  rw [hpv, smul_dotProduct, hw, hpv, smul_dotProduct, E.value_netOutput h]
  ring

/-- Surplus value is positive exactly when the value of labour power is below
one (given positive employment). -/
theorem surplusValue_pos_iff {b : ι → ℝ} {x : ι → ℝ}
    (hL : 0 < E.employment x) :
    0 < E.surplusValue b x ↔ E.valueOfLabourPower b < 1 := by
  unfold surplusValue
  constructor <;> intro h <;> nlinarith

/-- **Exploitation and profit have the same sign** under the correspondence,
for a positive multiplier. -/
theorem profit_pos_iff_surplusValue_pos (h : E.Productive) {p : ι → ℝ}
    {k w : ℝ} {b : ι → ℝ} (hpv : p = k • E.value) (hw : w = p ⬝ᵥ b)
    (hk : 0 < k) (x : ι → ℝ) :
    0 < E.profit p w x ↔ 0 < E.surplusValue b x := by
  rw [E.profit_eq_surplusValue h hpv hw x]
  exact mul_pos_iff_of_pos_left hk

/-- **The profit rate is the value rate of profit.** Under the correspondence
the money profit rate `r` of the price system equals surplus value over
constant plus variable capital; the multiplier `k` cancels. -/
theorem profitRate_eq_valueProfitRate (h : E.Productive) {p : ι → ℝ}
    {r w k : ℝ} {b : ι → ℝ} {x : ι → ℝ}
    (hp : E.IsPriceSystem p r w) (hpv : p = k • E.value)
    (hw : w = p ⬝ᵥ b) (hk : k ≠ 0)
    (hden : E.constantCapital x + E.variableCapital b x ≠ 0) :
    r = E.valueProfitRate b x := by
  have hprofit : E.profit p w x = r * (E.capitalAdvanced p x + E.wageBill w x) :=
    E.profit_eq hp x
  have hP : E.profit p w x = k * E.surplusValue b x :=
    E.profit_eq_surplusValue h hpv hw x
  have hC : E.capitalAdvanced p x + E.wageBill w x
      = k * (E.constantCapital x + E.variableCapital b x) := by
    unfold capitalAdvanced wageBill constantCapital variableCapital valueOfLabourPower
    rw [hpv, smul_dotProduct, hw, hpv, smul_dotProduct]
    ring
  have hc : E.surplusValue b x
      = r * (E.constantCapital x + E.variableCapital b x) := by
    have h' : k * E.surplusValue b x
        = k * (r * (E.constantCapital x + E.variableCapital b x)) := by
      rw [← hP, hprofit, hC]
      ring
    exact mul_left_cancel₀ hk h'
  unfold valueProfitRate
  rw [eq_div_iff hden]
  linarith [hc]

end Economy

end LeanMarx
