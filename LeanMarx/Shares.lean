import LeanMarx.RentTheory

set_option linter.unusedSectionVars false

/-!
# Monopoly, the wage share and the capital share

The price decomposition `P = w L + R` turns into a split of net output:

`wageShare = w L / P`, `capitalShare = R / P`, with `wageShare + capitalShare = 1`.

Using `R = w · (Σ_{monopolised c} μ c v c y c)`, the wage share is

`wageShare = 1 / (1 + V / L)`,   `V = Σ_{monopolised c} μ c v c y c`,

so the wage level cancels: the split is determined by the **value-weighted
rent** `V` per unit of labour, not by the number of monopolies and not by `w`.

More or larger monopolies raise `V` and lower the wage share; the capital
share rises correspondingly.  A single large monopoly can outweigh many small
ones, so the count alone does not determine the spread.
-/

namespace LeanMarx

open Classical Finset Matrix

variable {ι φ : Type*} [Fintype ι] [Fintype φ] [DecidableEq ι] [DecidableEq φ]

/-- Wage bill in value terms. -/
noncomputable def wageBillValue (v y : ι → ℝ) (w : ℝ) : ℝ :=
  w * aggregateLabour v y

/-- Value-weighted rent over a set of monopolised commodities. -/
noncomputable def valueRentOn (v : ι → ℝ) (μ : ι → ℝ) (y : ι → ℝ)
    (S : Finset ι) : ℝ :=
  ∑ c ∈ S, μ c * v c * y c

theorem valueRentOn_mono_set {v μ y : ι → ℝ} {S T : Finset ι} (h : S ⊆ T)
    (hμ : ∀ c, 0 ≤ μ c) (hv : ∀ c, 0 ≤ v c) (hy : ∀ c, 0 ≤ y c) :
    valueRentOn v μ y S ≤ valueRentOn v μ y T := by
  unfold valueRentOn
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun c _ _ => mul_nonneg (mul_nonneg (hμ c) (hv c)) (hy c))

namespace ProducerTable

variable (T : ProducerTable ι φ) (v : ι → ℝ) (w : ℝ) (μ : ι → ℝ) (y : ι → ℝ)

/-- Value rent over the commodities that are actually monopolised. -/
noncomputable def valueRent : ℝ :=
  valueRentOn v μ y (Finset.univ.filter (fun c => T.IsMonopoly c))

/-- Price of net output. -/
noncomputable def netOutputValue : ℝ :=
  aggregatePrice (T.marketPrice v w μ) y

/-- Wage share of net output. -/
noncomputable def wageShare : ℝ :=
  wageBillValue v y w / T.netOutputValue v w μ y

/-- Capital (rent) share of net output. -/
noncomputable def capitalShare : ℝ :=
  T.aggregateRent v w μ y / T.netOutputValue v w μ y

/-- Net output is the wage bill plus rent. -/
theorem netOutputValue_eq :
    T.netOutputValue v w μ y = wageBillValue v y w + T.aggregateRent v w μ y := by
  unfold netOutputValue wageBillValue
  rw [aggregatePrice_eq_labour_add_rent]

/-- Rent is `w` times the value-weighted rent. -/
theorem aggregateRent_eq_w_mul_valueRent :
    T.aggregateRent v w μ y = w * T.valueRent v μ y := by
  rw [aggregateRent_eq_sum_monopolies]
  unfold valueRent valueRentOn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The two shares add to one.** -/
theorem wageShare_add_capitalShare (hP : T.netOutputValue v w μ y ≠ 0) :
    T.wageShare v w μ y + T.capitalShare v w μ y = 1 := by
  unfold wageShare capitalShare
  rw [← add_div, netOutputValue_eq]
  exact div_self (by rwa [netOutputValue_eq] at hP)

/-- The wage share as `1 / (1 + R/(wL))`. -/
theorem wageShare_eq_inv (hwL : wageBillValue v y w ≠ 0) :
    T.wageShare v w μ y
      = 1 / (1 + T.aggregateRent v w μ y / wageBillValue v y w) := by
  unfold wageShare
  rw [netOutputValue_eq]
  field_simp

/-- **The wage level cancels.** The wage share depends on the value rent per
unit of labour, not on `w` or on the number of monopolies as such. -/
theorem wageShare_eq_valueRent (hw : w ≠ 0) (hL : aggregateLabour v y ≠ 0) :
    T.wageShare v w μ y = 1 / (1 + T.valueRent v μ y / aggregateLabour v y) := by
  rw [wageShare_eq_inv]
  · congr 1
    rw [aggregateRent_eq_w_mul_valueRent]
    unfold wageBillValue
    rw [mul_div_mul_left _ _ hw]
  · unfold wageBillValue
    exact mul_ne_zero hw hL

/-- The capital share as `(V/L) / (1 + V/L)`. -/
theorem capitalShare_eq_valueRent (hw : w ≠ 0) (hL : aggregateLabour v y ≠ 0) :
    T.capitalShare v w μ y
      = (T.valueRent v μ y / aggregateLabour v y)
        / (1 + T.valueRent v μ y / aggregateLabour v y) := by
  unfold capitalShare
  rw [netOutputValue_eq, aggregateRent_eq_w_mul_valueRent]
  unfold wageBillValue
  field_simp [hw, hL]

/-- **More rent lowers the wage share.** -/
theorem wageShare_antitone_valueRent {μ₁ μ₂ : ι → ℝ}
    (hw : w ≠ 0) (hL : 0 < aggregateLabour v y)
    (h₁ : 0 ≤ T.valueRent v μ₁ y)
    (h : T.valueRent v μ₁ y ≤ T.valueRent v μ₂ y) :
    T.wageShare v w μ₂ y ≤ T.wageShare v w μ₁ y := by
  rw [wageShare_eq_valueRent T v w μ₂ y hw hL.ne',
    wageShare_eq_valueRent T v w μ₁ y hw hL.ne']
  have hd₁ : 0 < 1 + T.valueRent v μ₁ y / aggregateLabour v y := by
    have := h₁
    positivity
  have hd₂ : 0 < 1 + T.valueRent v μ₂ y / aggregateLabour v y := by
    have h₂ : 0 ≤ T.valueRent v μ₂ y := le_trans h₁ h
    positivity
  rw [div_le_div_iff₀ hd₂ hd₁]
  have hdiv : T.valueRent v μ₁ y / aggregateLabour v y
      ≤ T.valueRent v μ₂ y / aggregateLabour v y :=
    (div_le_div_iff_of_pos_right hL).2 h
  nlinarith

/-- **More rent raises the capital share.** -/
theorem capitalShare_monotone_rent {a R₁ R₂ : ℝ} (ha : 0 < a) (hR₁ : 0 ≤ R₁)
    (h : R₁ ≤ R₂) : R₁ / (a + R₁) ≤ R₂ / (a + R₂) := by
  have h₁ : 0 < a + R₁ := by linarith
  have h₂ : 0 < a + R₂ := by linarith
  rw [div_le_div_iff₀ h₁ h₂]
  nlinarith

end ProducerTable

end LeanMarx
