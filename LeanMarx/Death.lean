import LeanMarx.Selection

set_option linter.unusedSectionVars false

/-!
# Stochastic death around the average profit rate

A producer that does not operate at the average profit rate has trouble
obtaining capital.  Model this as a **stochastic death probability**: the
producer's rate is compared with the capital-weighted average `r̄`, and the
probability of death is the lower tail of a Gaussian centred at `r̄`,

`deathProb r r̄ σ = Φ ((r̄ - r) / σ)`,

where `Φ` is the standard normal CDF.  Equivalently: the producer survives if
a Gaussian shock around its own rate leaves it at or above the average.

Properties:

* `deathProb` is a probability (`0 ≤ · ≤ 1`) and is antitone in the rate:
  lower rates die more often;
* at the average it is `1/2`, below the average at least `1/2`, above it at
  most `1/2`;
* deviations from the capital-weighted average sum to zero, so death prunes
  the lower tail and the survivors' expected growth is increasing in the rate.

This is the stochastic ingredient the deterministic selection models lacked.
A stationary power law still requires a full stochastic process with entry
and a stationary distribution; the module provides the death rule and the
one-period selection inequalities.
-/

namespace LeanMarx

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! ## The standard normal CDF -/

/-- Standard normal cumulative distribution function. -/
noncomputable def normalCdf (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, gaussianPDFReal 0 1 t

theorem normalCdf_nonneg (x : ℝ) : 0 ≤ normalCdf x :=
  setIntegral_nonneg measurableSet_Iic
    (fun t _ => gaussianPDFReal_nonneg 0 1 t)

theorem normalCdf_le_one (x : ℝ) : normalCdf x ≤ 1 := by
  have h := setIntegral_le_integral (s := Set.Iic x) (f := fun t => gaussianPDFReal 0 1 t)
    (integrable_gaussianPDFReal 0 1) (ae_of_all _ (fun t => gaussianPDFReal_nonneg 0 1 t))
  rwa [integral_gaussianPDFReal_eq_one 0 one_ne_zero] at h

theorem normalCdf_mono : Monotone normalCdf := by
  intro x y hxy
  exact setIntegral_mono_set (f := fun t => gaussianPDFReal 0 1 t)
    (integrable_gaussianPDFReal 0 1).integrableOn
    (ae_of_all _ (fun t => gaussianPDFReal_nonneg 0 1 t))
    (ae_of_all _ (fun t ht => le_trans ht hxy))

/-- The Gaussian used below is even. -/
theorem gaussianPDFReal_zero_one_neg (t : ℝ) :
    gaussianPDFReal 0 1 (-t) = gaussianPDFReal 0 1 t := by
  unfold gaussianPDFReal
  simp only [sub_zero, neg_sq]

/-- `Φ 0 = 1/2`: the symmetry of the Gaussian about zero. -/
theorem normalCdf_zero : normalCdf 0 = 1 / 2 := by
  set f : ℝ → ℝ := fun t => gaussianPDFReal 0 1 t with hf
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Iic, Set.mem_Ioi] at hx hx'
    exact absurd hx' (not_lt.mpr hx)
  have hunion : Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    by_cases h : x ≤ 0
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge h)
  have hsplit : (∫ t in Set.Iic (0 : ℝ), f t) + (∫ t in Set.Ioi (0 : ℝ), f t)
      = ∫ t, f t := by
    rw [← setIntegral_union hdisj measurableSet_Ioi
      (integrable_gaussianPDFReal 0 1).integrableOn
      (integrable_gaussianPDFReal 0 1).integrableOn, hunion]
    simp [hf]
  have hsym : (∫ t in Set.Ioi (0 : ℝ), f t) = ∫ t in Set.Iic (0 : ℝ), f t := by
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    have hcongr : (∫ x in Set.Ioi (0 : ℝ), f (-x)) = ∫ x in Set.Ioi (0 : ℝ), f x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact gaussianPDFReal_zero_one_neg x
    rw [hcongr] at h
    simpa using h
  have htotal : (∫ t, f t) = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have h2 : (∫ t in Set.Iic (0 : ℝ), f t) + (∫ t in Set.Iic (0 : ℝ), f t) = 1 := by
    nth_rewrite 2 [← hsym]
    rw [hsplit, htotal]
  unfold normalCdf
  change (∫ t in Set.Iic (0 : ℝ), f t) = 1 / 2
  linarith

/-! ## Death probability -/

/-- Probability of death for a producer with rate `r` when the average rate is
`r̄` and the Gaussian scale is `σ`. -/
noncomputable def deathProb (r rbar σ : ℝ) : ℝ :=
  normalCdf ((rbar - r) / σ)

theorem deathProb_nonneg (r rbar σ : ℝ) : 0 ≤ deathProb r rbar σ :=
  normalCdf_nonneg _

theorem deathProb_le_one (r rbar σ : ℝ) : deathProb r rbar σ ≤ 1 :=
  normalCdf_le_one _

/-- Lower rates die more often. -/
theorem deathProb_antitone {rbar σ : ℝ} (hσ : 0 < σ) :
    Antitone (fun r => deathProb r rbar σ) := by
  intro r₁ r₂ h
  apply normalCdf_mono
  exact div_le_div_of_nonneg_right (by linarith : rbar - r₂ ≤ rbar - r₁) hσ.le

/-- At the average the death probability is one half. -/
theorem deathProb_avg {rbar σ : ℝ} : deathProb rbar rbar σ = 1 / 2 := by
  unfold deathProb
  rw [sub_self, zero_div, normalCdf_zero]

/-- Below the average, death is at least a coin flip. -/
theorem deathProb_below_avg {r rbar σ : ℝ} (hσ : 0 < σ) (h : r < rbar) :
    1 / 2 ≤ deathProb r rbar σ := by
  rw [← deathProb_avg]
  exact deathProb_antitone hσ h.le

/-- Above the average, death is at most a coin flip. -/
theorem deathProb_above_avg {r rbar σ : ℝ} (hσ : 0 < σ) (h : rbar < r) :
    deathProb r rbar σ ≤ 1 / 2 := by
  rw [← deathProb_avg]
  exact deathProb_antitone hσ h.le

/-! ## The average rate -/

variable {φ : Type*} [Fintype φ]

/-- Capital-weighted average profit rate. -/
noncomputable def averageRate (K r : φ → ℝ) : ℝ :=
  (∑ p, K p * r p) / ∑ p, K p

/-- **Deviations from the average sum to zero.** Below-average and
above-average producers balance exactly. -/
theorem sum_deviation_eq_zero (K r : φ → ℝ) (hK : ∑ p, K p ≠ 0) :
    ∑ p, K p * (r p - averageRate K r) = 0 := by
  have h : (∑ p, K p * (r p - averageRate K r))
      = (∑ p, K p * r p) - (∑ p, K p) * averageRate K r := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [h, averageRate, mul_div_cancel₀ _ hK]
  ring

/-! ## Expected growth -/

/-- Survival probability. -/
noncomputable def survivalProb (r rbar σ : ℝ) : ℝ := 1 - deathProb r rbar σ

/-- Expected gross capital factor: survive with probability `1 - d`, then grow
by `1 + r`. -/
noncomputable def expectedGrowth (r rbar σ : ℝ) : ℝ :=
  survivalProb r rbar σ * (1 + r)

/-- **Selection by expected growth.** Higher rates have higher expected
growth, because death is less likely above the average. -/
theorem expectedGrowth_le_of_le {r₁ r₂ rbar σ : ℝ} (hσ : 0 < σ) (h : r₁ ≤ r₂)
    (hr₁ : -1 ≤ r₁) :
    expectedGrowth r₁ rbar σ ≤ expectedGrowth r₂ rbar σ := by
  have hd : deathProb r₂ rbar σ ≤ deathProb r₁ rbar σ := deathProb_antitone hσ h
  have hs : survivalProb r₁ rbar σ ≤ survivalProb r₂ rbar σ := by
    unfold survivalProb
    linarith
  have hg : 1 + r₁ ≤ 1 + r₂ := by linarith
  have hc : 0 ≤ 1 + r₁ := by linarith
  have hb : 0 ≤ survivalProb r₂ rbar σ := by
    unfold survivalProb
    linarith [deathProb_le_one r₂ rbar σ]
  unfold expectedGrowth
  exact mul_le_mul hs hg hc hb

end LeanMarx
