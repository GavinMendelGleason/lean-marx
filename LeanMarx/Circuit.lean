import LeanMarx.Distribution

set_option linter.unusedSectionVars false

/-!
# The circuit of capital and scale-free shares

One turn of the circuit `M → C → P → C′ → M′` at a **uniform** profit rate
scales every investor's capital by the same factor `1 + π`.  This module
records what that does to the distribution of investor shares:

* every investor's share of total capital is invariant (`circuitStep_share`);
* every scale-free inequality measure is invariant, in particular the Gini
  coefficient (`gini_smul`);
* the set of investors above a capital threshold is the same set with the
  threshold rescaled (`circuitStep_exceedance`).

So the time evolution of the uniform circuit cannot create a Pareto
distribution: it preserves whatever share distribution the initial
endowments had, and can only relabel thresholds.  A power law would require
heterogeneity the circuit does not have — differential profit rates,
idiosyncratic multiplicative shocks with a reflecting barrier or reset, or a
rich-get-richer mechanism.  Pure multiplicative growth with independent
shocks (Gibrat) tends to a lognormal cross-section, not a Pareto one, unless
a lower barrier or reset is added.

The development is single-period elsewhere; this is the minimal one-step
circuit, not a dynamic model with accumulation, saving or entry.
-/

namespace LeanMarx

open Finset

variable {κ : Type*} [Fintype κ]

/-- An investor's share of a total. -/
noncomputable def share (w : κ → ℝ) (i : κ) : ℝ := w i / ∑ j, w j

/-- One turn of the circuit at the uniform profit rate `π`: every investor's
capital is scaled by `1 + π`. -/
def circuitStep (π : ℝ) (w : κ → ℝ) : κ → ℝ := (1 + π) • w

theorem sum_circuitStep (π : ℝ) (w : κ → ℝ) :
    ∑ i, circuitStep π w i = (1 + π) * ∑ i, w i := by
  simp [circuitStep, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- **Scaling preserves shares.** -/
theorem share_smul (c : ℝ) (hc : c ≠ 0) (w : κ → ℝ) (hS : ∑ i, w i ≠ 0)
    (i : κ) : share (c • w) i = share w i := by
  unfold share
  have hsum : ∑ j, (c • w) j = c * ∑ j, w j := by
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [hsum]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hden : c * ∑ i, w i ≠ 0 := mul_ne_zero hc hS
  field_simp

/-- **Uniform accumulation preserves shares.** After one turn of the circuit
every investor holds the same share as before. -/
theorem circuitStep_share (π : ℝ) (w : κ → ℝ) (h : 1 + π ≠ 0)
    (hS : ∑ i, w i ≠ 0) (i : κ) :
    share (circuitStep π w) i = share w i :=
  share_smul (1 + π) h w hS i

/-- **Uniform scaling preserves the Gini coefficient** (indeed every
scale-free inequality measure). -/
theorem gini_smul {c : ℝ} (hc : 0 < c) (w : κ → ℝ) :
    gini (c • w) = gini w := by
  unfold gini
  have hsum : ∑ i, (c • w) i = c * ∑ i, w i := by
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have habs : ∀ i j, |(c • w) i - (c • w) j| = c * |w i - w j| := by
    intro i j
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul,
      abs_of_pos hc]
  simp_rw [habs]
  have hnum : (∑ i, ∑ j, c * |w i - w j|)
      = c * (∑ i, ∑ j, |w i - w j|) := by
    simp_rw [← Finset.mul_sum]
  rw [hnum, hsum]
  rw [show (2 * (Fintype.card κ : ℝ)) * (c * ∑ i, w i)
      = c * ((2 * (Fintype.card κ : ℝ)) * ∑ i, w i) by ring]
  rw [mul_div_mul_left _ _ hc.ne']

/-- **The circuit relabels thresholds; it does not reshape the
distribution.** The investors above a capital threshold after one turn are
exactly those above the rescaled threshold before it. -/
theorem circuitStep_exceedance (π : ℝ) (h : 0 < 1 + π) (w : κ → ℝ) (y : ℝ) :
    {i : κ | y < circuitStep π w i} = {i : κ | y / (1 + π) < w i} := by
  ext i
  simp only [Set.mem_ofPred_eq, circuitStep, Pi.smul_apply, smul_eq_mul]
  rw [div_lt_iff₀' h]

end LeanMarx
