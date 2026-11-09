import LeanMarx.SocialMetabolism
import LeanMarx.Demand

set_option linter.unusedSectionVars false

/-!
# A theory of rent: μ from the price–labour distance

Rent is the distance between the integrated labour time embodied in a
commodity and its price.  With labour value `v c`, wage `w` and price `p c`,

`rentRate p v w c = p c / (w · v c) − 1 = (p c − w · v c) / (w · v c)`,

so the observed price–labour gap *is* μ (`rentRate_eq_price_gap`), and if the
price is `(1 + μ) w v` the gap recovers μ exactly
(`rentRate_eq_of_rate`).

A theory of what determines μ: a monopolist facing **linear demand**
`q(p) = a − b p` and unit cost `c = w · v` maximizes `(p − c)(a − b p)`.

* the profit-maximising price is `p* = (a + b c)/(2b)` (`monopolyPrice`);
* the resulting markup is `μ = (a − b c)/(2 b c)` (`monopolyMarkup`);
* equivalently `μ = 1/(ε − 1)` where `ε` is the absolute demand elasticity at
  `p*` (`monopolyMarkup_eq_inv_elasticity`);
* more elastic demand (larger `b`) gives a smaller μ
  (`monopolyMarkup_antitone_elastic`);
* under competition — two or more producers — the wedge is zero
  (`rent_eq_zero_of_two_producers`).

So rent has two determinants: **market power** (demand elasticity) sets the
potential μ, and **contestability** (entry) decides whether it survives.
-/

namespace LeanMarx

open Classical Finset Matrix

variable {ι φ : Type*} [Fintype ι] [Fintype φ] [DecidableEq ι] [DecidableEq φ]

/-! ## Measuring rent from the gap -/

/-- Rent is the normalized difference between price and integrated labour
time. -/
theorem rentRate_eq_price_gap {p v : ι → ℝ} {w : ℝ} {c : ι}
    (hw : w ≠ 0) (hv : v c ≠ 0) :
    rentRate p v w c = (p c - w * v c) / (w * v c) := by
  unfold rentRate
  field_simp [hw, hv]

/-- **The gap recovers μ.** If the price is `(1 + μ) w v`, the measured rent
rate is μ. -/
theorem rentRate_eq_of_rate {p v : ι → ℝ} {w μ : ℝ} {c : ι}
    (h : p c = (1 + μ) * (w * v c)) (hw : w ≠ 0) (hv : v c ≠ 0) :
    rentRate p v w c = μ := by
  unfold rentRate
  rw [h]
  field_simp [hw, hv]
  ring

/-! ## Monopoly pricing with linear demand -/

/-- Linear demand `q(p) = a − b p`. -/
noncomputable def linearDemand (a b p : ℝ) : ℝ := a - b * p

/-- Monopoly profit at price `p`, unit cost `c`. -/
noncomputable def monopolyProfit (a b c p : ℝ) : ℝ :=
  (p - c) * linearDemand a b p

/-- Profit-maximising price. -/
noncomputable def monopolyPrice (a b c : ℝ) : ℝ := (a + b * c) / (2 * b)

/-- The rent rate at the monopoly price. -/
noncomputable def monopolyMarkup (a b c : ℝ) : ℝ := (a - b * c) / (2 * b * c)

/-- The monopoly price maximizes profit. -/
theorem monopolyProfit_le {a b c : ℝ} (hb : 0 < b) (p : ℝ) :
    monopolyProfit a b c p ≤ monopolyProfit a b c (monopolyPrice a b c) := by
  have hid : monopolyProfit a b c (monopolyPrice a b c) - monopolyProfit a b c p
      = b * (p - monopolyPrice a b c) ^ 2 := by
    unfold monopolyProfit linearDemand monopolyPrice
    field_simp
    ring
  have hnonneg : 0 ≤ b * (p - monopolyPrice a b c) ^ 2 :=
    mul_nonneg hb.le (sq_nonneg _)
  linarith

/-- The monopoly price is cost times `1 + μ`. -/
theorem monopolyPrice_eq_cost_mul {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0) :
    monopolyPrice a b c = (1 + monopolyMarkup a b c) * c := by
  unfold monopolyPrice monopolyMarkup
  field_simp
  ring

/-- Monopoly rent is positive when the market is profitable. -/
theorem monopolyMarkup_pos {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (h : b * c < a) : 0 < monopolyMarkup a b c := by
  unfold monopolyMarkup
  exact div_pos (by nlinarith) (by positivity)

/-- **More elastic demand gives a smaller rent.** -/
theorem monopolyMarkup_antitone_elastic {a b₁ b₂ c : ℝ}
    (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : b₁ < b₂) (hc : 0 < c)
    (hbc : b₂ * c < a) :
    monopolyMarkup a b₂ c < monopolyMarkup a b₁ c := by
  unfold monopolyMarkup
  have hb₂pos : 0 < b₂ := lt_trans hb₁ hb₂
  have h₂ : 0 < 2 * b₂ * c := by positivity
  have h₁ : 0 < 2 * b₁ * c := by positivity
  rw [div_lt_div_iff₀ h₂ h₁]
  have hab : a * b₁ * c < a * b₂ * c := by
    have h' : a * b₁ < a * b₂ := mul_lt_mul_of_pos_left hb₂ ha
    exact mul_lt_mul_of_pos_right h' hc
  nlinarith

/-- Absolute demand elasticity of linear demand. -/
noncomputable def demandElasticity (a b p : ℝ) : ℝ := b * p / (a - b * p)

/-- Elasticity at the monopoly price. -/
noncomputable def monopolyElasticity (a b c : ℝ) : ℝ :=
  demandElasticity a b (monopolyPrice a b c)

/-- **The Lerner identity.** At the monopoly price the markup is
`1/(ε − 1)`. -/
theorem monopolyElasticity_sub_one {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : a - b * c ≠ 0) :
    monopolyElasticity a b c - 1 = (2 * b * c) / (a - b * c) := by
  have hp : b * monopolyPrice a b c = (a + b * c) / 2 := by
    unfold monopolyPrice
    field_simp [hb]
  have hq : a - b * monopolyPrice a b c = (a - b * c) / 2 := by
    unfold monopolyPrice
    field_simp [hb]
    ring
  unfold monopolyElasticity demandElasticity
  rw [hq, hp]
  field_simp [habc]
  ring

theorem monopolyMarkup_eq_inv_elasticity {a b c : ℝ} (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : a - b * c ≠ 0) :
    monopolyMarkup a b c = 1 / (monopolyElasticity a b c - 1) := by
  rw [monopolyElasticity_sub_one hb hc habc]
  unfold monopolyMarkup
  field_simp [habc]

/-! ## The determined rent rate -/

namespace ProducerTable

/-- The rent rate determined by the theory: the monopoly markup where there is
a single producer, and zero where there is competition. -/
noncomputable def determinedMarkup (T : ProducerTable ι φ) (a b : ι → ℝ)
    (v : ι → ℝ) (w : ℝ) (c : ι) : ℝ :=
  if T.IsMonopoly c then monopolyMarkup (a c) (b c) (w * v c) else 0

theorem determinedMarkup_of_monopoly (T : ProducerTable ι φ) {a b : ι → ℝ}
    {v : ι → ℝ} {w : ℝ} {c : ι} (h : T.IsMonopoly c) :
    T.determinedMarkup a b v w c = monopolyMarkup (a c) (b c) (w * v c) := by
  unfold determinedMarkup
  rw [if_pos h]

theorem determinedMarkup_of_not_monopoly (T : ProducerTable ι φ) {a b : ι → ℝ}
    {v : ι → ℝ} {w : ℝ} {c : ι} (h : ¬ T.IsMonopoly c) :
    T.determinedMarkup a b v w c = 0 := by
  unfold determinedMarkup
  rw [if_neg h]

/-- **Determined prices.** With the determined markup, the market price is the
monopoly price where one producer exists and the labour value where it does
not. -/
theorem marketPrice_determined (T : ProducerTable ι φ) {a b : ι → ℝ}
    {v : ι → ℝ} {w : ℝ} {c : ι} :
    T.marketPrice v w (T.determinedMarkup a b v w) c
      = if T.IsMonopoly c then (1 + monopolyMarkup (a c) (b c) (w * v c)) * (w * v c)
        else w * v c := by
  unfold ProducerTable.marketPrice determinedMarkup
  by_cases h : T.IsMonopoly c
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    ring

end ProducerTable

end LeanMarx
