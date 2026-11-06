import LeanMarx.Investment

set_option linter.unusedSectionVars false

/-!
# Investment according to expected profit rates

Investors allocate capital across activities according to the **expected
profit rate** of each activity.  With expected rates `r : σ → ℝ` and an
investor's capital `M i`, the share placed in activity `a` is

`rateShare r a = r a / Σ b, r b`,

so the aggregate capital placed in `a` is `(Σ i, M i) * rateShare r a`,
independent of how wealth is distributed across investors.

If every investor uses the same expected rates, each earns the rate-weighted
average

`ρ̄ = (Σ a, (r a)^2) / (Σ a, r a)`,

so every capital is multiplied by `1 + ρ̄` and the distribution of wealth is
invariant: shares and the Gini coefficient do not move.  Differences in
wealth shares therefore cannot come from common expectations about profit
rates; they come from **heterogeneous expectations**.  An investor whose
expected return exceeds the economy-wide average gains share
(`share_increases_iff_above_average`), and one below it loses.
-/

namespace LeanMarx

open Finset Matrix

variable {κ σ : Type*} [Fintype κ] [Fintype σ] [DecidableEq κ] [DecidableEq σ]

/-! ## Allocating by expected profit rates -/

/-- Share of an investor's capital placed in activity `a`, proportional to
its expected profit rate. -/
noncomputable def rateShare (r : σ → ℝ) (a : σ) : ℝ := attachProb r a

theorem rateShare_nonneg {r : σ → ℝ} (hr : ∀ a, 0 ≤ r a)
    (hR : 0 < ∑ a, r a) (a : σ) : 0 ≤ rateShare r a :=
  attachProb_nonneg hr hR a

theorem sum_rateShare {r : σ → ℝ} (hR : ∑ a, r a ≠ 0) :
    ∑ a, rateShare r a = 1 :=
  sum_attachProb hR

theorem rateShare_strictMono {r : σ → ℝ} (hR : 0 < ∑ a, r a) {a b : σ}
    (h : r a < r b) : rateShare r a < rateShare r b :=
  attachProb_strictMono hR h

theorem rateShare_eq_zero {r : σ → ℝ} {a : σ} (ha : r a = 0) : rateShare r a = 0 := by
  simp [rateShare, attachProb, ha]

/-- Investment of investor `i` in activity `a`. -/
noncomputable def investIn (M : κ → ℝ) (r : σ → ℝ) (i : κ) (a : σ) : ℝ :=
  M i * rateShare r a

/-- Aggregate capital placed in activity `a`. -/
noncomputable def totalInvested (M : κ → ℝ) (r : σ → ℝ) (a : σ) : ℝ :=
  ∑ i, investIn M r i a

/-- **Aggregate investment is proportional to the expected rate, whatever the
distribution of wealth.** -/
theorem totalInvested_eq (M : κ → ℝ) (r : σ → ℝ) (a : σ) :
    totalInvested M r a = (∑ i, M i) * rateShare r a := by
  unfold totalInvested investIn
  rw [Finset.sum_mul]

/-! ## The expected return rate -/

/-- The return rate an investor expects, if the expected rates are realised:
the rate-weighted average of the expected rates. -/
noncomputable def expectedReturnRate (r : σ → ℝ) : ℝ :=
  ∑ a, r a * rateShare r a

/-- The expected return rate in closed form. -/
theorem expectedReturnRate_eq {r : σ → ℝ} (hR : ∑ a, r a ≠ 0) :
    expectedReturnRate r = (∑ a, (r a) ^ 2) / ∑ a, r a := by
  unfold expectedReturnRate rateShare attachProb
  have hterm : ∀ a, r a * (r a / ∑ b, r b) = (r a) ^ 2 / ∑ b, r b := by
    intro a
    field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div]

/-- Wealth after the expected rates are realised. -/
noncomputable def expectedWealth (M : κ → ℝ) (r : σ → ℝ) : κ → ℝ :=
  fun i => M i * (1 + expectedReturnRate r)

theorem expectedWealth_eq_smul (M : κ → ℝ) (r : σ → ℝ) :
    expectedWealth M r = (1 + expectedReturnRate r) • M := by
  ext i
  simp [expectedWealth, smul_eq_mul, mul_comm]

/-- **Common expected rates preserve the wealth distribution.** Every
investor's capital is multiplied by the same factor `1 + ρ̄`, so shares and
the Gini coefficient are unchanged. -/
theorem expectedWealth_share {M : κ → ℝ} {r : σ → ℝ}
    (hscale : 1 + expectedReturnRate r ≠ 0) (hM : ∑ i, M i ≠ 0) (i : κ) :
    share (expectedWealth M r) i = share M i := by
  rw [expectedWealth_eq_smul]
  exact share_smul _ hscale M hM i

theorem expectedWealth_gini {M : κ → ℝ} {r : σ → ℝ}
    (hscale : 0 < 1 + expectedReturnRate r) :
    gini (expectedWealth M r) = gini M := by
  rw [expectedWealth_eq_smul]
  exact gini_smul hscale M

/-! ## Heterogeneous expectations -/

/-- Wealth when each investor's own expected rates are realised. -/
noncomputable def expectedWealthOf (M : κ → ℝ) (r : κ → σ → ℝ) : κ → ℝ :=
  fun i => M i * (1 + expectedReturnRate (r i))

/-- **Above-average expectations gain share.** An investor's share rises
exactly when their gross expected return exceeds the economy-wide average
gross return. -/
theorem share_increases_iff_above_average [Nonempty κ] {M ρ : κ → ℝ}
    (hM : ∀ i, 0 < M i) (hY : 0 < ∑ i, M i * (1 + ρ i)) (i : κ) :
    M i / (∑ k, M k) < (M i * (1 + ρ i)) / (∑ k, M k * (1 + ρ k))
      ↔ (∑ k, M k * (1 + ρ k)) / (∑ k, M k) < 1 + ρ i := by
  have hW : 0 < ∑ k, M k :=
    Finset.sum_pos (fun k _ => hM k) Finset.univ_nonempty
  rw [div_lt_div_iff₀ hW hY, div_lt_iff₀ hW]
  constructor <;> intro h <;> nlinarith [hM i]

end LeanMarx
