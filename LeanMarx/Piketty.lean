import LeanMarx.Dynamics

set_option linter.unusedSectionVars false

/-!
# `r` versus `g`: the aggregate wealth pump

Piketty's comparison is between the return on capital `r` and the growth rate
`g`.  The model already has both objects: `Dynamics.wealthAt π w0 t` grows
capital at the profit rate `π`, and `Dynamics.BalancedPath.g` is the balanced
growth rate of the economy.

* The wealth/income ratio grows iff `r > g`.
* With saving rate `s`, the capital/output ratio `β = K/Y` grows iff
  `s r > g`; the capital share is `α = r β`, so a rising `β` raises `α`.
* `r > g` raises the capital share relative to labour.  It does **not**, by
  itself, concentrate wealth among capitalists: a uniform return preserves
  shares (`Circuit.circuitStep_share`).  Concentration among owners needs
  heterogeneous returns or the entry/exit wealth pump of `WealthPump`.

Rent is a component of the return, not the whole of it; a higher rent rate
raises `r` and makes `r > g` more likely, but the mapping from rent to the
return on capital depends on how the rent is capitalized.
-/

namespace LeanMarx

open Filter
open scoped Topology

/-- Wealth/income ratio when wealth grows at `r` and income at `g`. -/
noncomputable def wealthIncomeRatio (r g W0 Y0 : ℝ) (t : ℕ) : ℝ :=
  W0 / Y0 * ((1 + r) / (1 + g)) ^ t

/-- **`r > g` makes the wealth/income ratio grow without bound.** -/
theorem wealthIncomeRatio_tendsto_atTop {r g W0 Y0 : ℝ} (hW : 0 < W0)
    (hY : 0 < Y0) (hg : 0 < 1 + g) (h : g < r) :
    Tendsto (wealthIncomeRatio r g W0 Y0) atTop atTop := by
  have hratio : 1 < (1 + r) / (1 + g) := by
    rw [lt_div_iff₀ hg]
    linarith
  have hpow : Tendsto (fun t : ℕ => ((1 + r) / (1 + g)) ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hratio
  have hc : 0 < W0 / Y0 := div_pos hW hY
  change Tendsto (fun t : ℕ => W0 / Y0 * ((1 + r) / (1 + g)) ^ t) atTop atTop
  simpa [mul_comm] using hpow.atTop_mul_const hc

/-- **`r < g` makes the wealth/income ratio vanish.** -/
theorem wealthIncomeRatio_tendsto_zero {r g W0 Y0 : ℝ} (hr : -1 < r)
    (hg : 0 < 1 + g) (h : r < g) :
    Tendsto (wealthIncomeRatio r g W0 Y0) atTop (𝓝 0) := by
  have hratio_pos : 0 ≤ (1 + r) / (1 + g) :=
    div_nonneg (by linarith) hg.le
  have hratio_lt : (1 + r) / (1 + g) < 1 := by
    rw [div_lt_iff₀ hg]
    linarith
  have hpow : Tendsto (fun t : ℕ => ((1 + r) / (1 + g)) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio_pos hratio_lt
  change Tendsto (fun t : ℕ => W0 / Y0 * ((1 + r) / (1 + g)) ^ t) atTop (𝓝 0)
  simpa [mul_comm] using hpow.mul_const (W0 / Y0)

/-- One step of the capital/output ratio with saving rate `s`: `β = K/Y`. -/
noncomputable def capitalOutputStep (s r g β : ℝ) : ℝ :=
  (1 + s * r) / (1 + g) * β

/-- **Piketty's second condition.** The capital/output ratio grows iff
`s r > g`. -/
theorem capitalOutput_grows_iff {s r g β : ℝ} (hβ : 0 < β) (hg : 0 < 1 + g)
    (hs : -1 < s * r) :
    β < capitalOutputStep s r g β ↔ g < s * r := by
  have hk : 0 < (1 + s * r) / (1 + g) := div_pos (by linarith) hg
  have hmul : β < (1 + s * r) / (1 + g) * β ↔ 1 < (1 + s * r) / (1 + g) := by
    rw [mul_comm]
    exact lt_mul_iff_one_lt_right hβ
  rw [capitalOutputStep, hmul]
  rw [lt_div_iff₀ hg]
  constructor <;> intro h <;> linarith

/-- The capital share `α = r β`. -/
noncomputable def capitalShare (r β : ℝ) : ℝ := r * β

/-- A higher capital/output ratio raises the capital share. -/
theorem capitalShare_strictMono_beta {r β₁ β₂ : ℝ} (hr : 0 < r) (h : β₁ < β₂) :
    capitalShare r β₁ < capitalShare r β₂ := by
  unfold capitalShare
  exact mul_lt_mul_of_pos_left h hr

end LeanMarx
