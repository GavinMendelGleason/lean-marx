import LeanMarx.Expectations

set_option linter.unusedSectionVars false

/-!
# Investment flows and the equalization tendency

Capital flows toward the higher profit rate.  In the two-sector linear model

`r i = α i − β K i`,   `I = γ (r₁ − r₂)`,

sector 1 receives investment `I` and sector 2 gives up `I`, so total capital
is conserved.  The gap evolves as

`g' = (1 − 2 β γ) g`.

So the gap shrinks geometrically when `0 < β γ < 1`, oscillates when
`β γ > 1/2`, and does not equalize when `β γ = 0`.  This is the classical
tendency, with its condition: the flow must be responsive (`γ > 0`) and the
rate must fall with capital (`β > 0`), but not so strongly that the flow
overshoots.

The model is the tendency only.  Barriers, rents, different capital
intensities, innovation and market power sustain dispersion; those are the
`RentTheory` and `ProfitDistribution` layers, not this one.
-/

namespace LeanMarx

open Filter
open scoped Topology

/-- A linear rate–capital relation `r = α − β K`. -/
noncomputable def linearRate (α β K : ℝ) : ℝ := α - β * K

/-- The rate gap between two sectors. -/
noncomputable def linearGap (α₁ α₂ β K₁ K₂ : ℝ) : ℝ :=
  linearRate α₁ β K₁ - linearRate α₂ β K₂

/-- Investment in sector 1, financed by sector 2, proportional to the gap. -/
noncomputable def gapInvestment (γ r₁ r₂ : ℝ) : ℝ := γ * (r₁ - r₂)

/-- One equalization step: capital flows to the high-rate sector. -/
noncomputable def equalizeStep (α₁ α₂ β γ K₁ K₂ : ℝ) : ℝ × ℝ :=
  let r₁ := linearRate α₁ β K₁
  let r₂ := linearRate α₂ β K₂
  let I := gapInvestment γ r₁ r₂
  (K₁ + I, K₂ - I)

/-- **The gap contracts by `1 − 2 β γ` in one step.** -/
theorem linearGap_step (α₁ α₂ β γ K₁ K₂ : ℝ) :
    linearGap α₁ α₂ β (equalizeStep α₁ α₂ β γ K₁ K₂).1
        (equalizeStep α₁ α₂ β γ K₁ K₂).2
      = (1 - 2 * β * γ) * linearGap α₁ α₂ β K₁ K₂ := by
  unfold equalizeStep linearGap linearRate gapInvestment
  ring

/-- One equalization step conserves total capital. -/
theorem equalizeStep_total (α₁ α₂ β γ K₁ K₂ : ℝ) :
    (equalizeStep α₁ α₂ β γ K₁ K₂).1 + (equalizeStep α₁ α₂ β γ K₁ K₂).2
      = K₁ + K₂ := by
  unfold equalizeStep gapInvestment
  ring

/-- The high-rate sector receives positive investment. -/
theorem gapInvestment_pos {γ r₁ r₂ : ℝ} (hγ : 0 < γ) (h : r₂ < r₁) :
    0 < gapInvestment γ r₁ r₂ := by
  unfold gapInvestment
  nlinarith

/-- The low-rate sector receives negative investment (it is a net seller). -/
theorem gapInvestment_neg {γ r₁ r₂ : ℝ} (hγ : 0 < γ) (h : r₁ < r₂) :
    gapInvestment γ r₁ r₂ < 0 := by
  unfold gapInvestment
  nlinarith

/-- The `t`-step capital path. -/
noncomputable def equalizePath (α₁ α₂ β γ K₁ K₂ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (K₁, K₂)
  | t + 1 =>
      equalizeStep α₁ α₂ β γ
        (equalizePath α₁ α₂ β γ K₁ K₂ t).1
        (equalizePath α₁ α₂ β γ K₁ K₂ t).2

/-- **The gap path is geometric.** -/
theorem gapPath_eq (α₁ α₂ β γ K₁ K₂ : ℝ) (t : ℕ) :
    linearGap α₁ α₂ β
        (equalizePath α₁ α₂ β γ K₁ K₂ t).1
        (equalizePath α₁ α₂ β γ K₁ K₂ t).2
      = (1 - 2 * β * γ) ^ t * linearGap α₁ α₂ β K₁ K₂ := by
  induction t with
  | zero => simp [equalizePath]
  | succ t ih =>
      rw [equalizePath, linearGap_step, ih, pow_succ]
      ring

/-- **The equalization tendency.** If `|1 − 2 β γ| < 1`, the rate gap tends
to zero: capital flows to the high-rate sector until the gap is arbitraged
away. -/
theorem gap_tendsto_zero (α₁ α₂ β γ K₁ K₂ : ℝ)
    (h : |1 - 2 * β * γ| < 1) :
    Tendsto (fun t : ℕ =>
      linearGap α₁ α₂ β
        (equalizePath α₁ α₂ β γ K₁ K₂ t).1
        (equalizePath α₁ α₂ β γ K₁ K₂ t).2) atTop (𝓝 0) := by
  have hpath : (fun t : ℕ =>
      linearGap α₁ α₂ β
        (equalizePath α₁ α₂ β γ K₁ K₂ t).1
        (equalizePath α₁ α₂ β γ K₁ K₂ t).2)
      = fun t : ℕ => (1 - 2 * β * γ) ^ t * linearGap α₁ α₂ β K₁ K₂ := by
    funext t
    rw [gapPath_eq]
  rw [hpath]
  have hnorm : ‖(1 - 2 * β * γ : ℝ)‖ < 1 := by
    simpa [Real.norm_eq_abs] using h
  simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).mul_const
    (linearGap α₁ α₂ β K₁ K₂)

end LeanMarx
