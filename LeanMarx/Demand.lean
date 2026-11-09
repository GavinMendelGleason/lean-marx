import LeanMarx.Distribution

set_option linter.unusedSectionVars false

/-!
# Demand, reproduction and the bottom

People have two ways to make money: sell labour power to firms, or earn a
return on capital invested in production.  They then split income between
consumption and investment.

* **Income.** `Population.income w π i = w · labour i + π · capital i`.
* **Subsistence.** A basket `b` of commodities is required to reproduce the
  worker.  Its cost is `subsistenceCost p b = p · b`.  Income below it means
  the worker cannot reproduce; the shortfall is `reproductionGap`.
* **Demand.** Preferences are a Stone–Geary / linear expenditure system: the
  basket `b` is bought first, and the surplus `y − p·b` is spent in fixed
  value shares `α`, `Σ α = 1`.  Below subsistence, demand is a rationed
  multiple of `b`.
* **Saving.** Investment is only possible out of the surplus:
  `0 ≤ s ≤ y − p·b`.  The remaining income `y − s` funds consumption;
  expenditure plus saving equals income (Walras' law at the individual
  level, and in aggregate).

The bottom pressure is the reproduction constraint: for a pure worker,
`w · labour ≥ p · b`, i.e. `w ≥ (p·b)/labour`.  Below that wage the worker's
full labour endowment cannot buy the subsistence basket, and the worker is
rationed below `b`.
-/

namespace LeanMarx

open Classical Finset Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ## Subsistence and reproduction -/

/-- Cost of the subsistence basket. -/
noncomputable def subsistenceCost (p b : ι → ℝ) : ℝ := p ⬝ᵥ b

/-- The amount by which income falls short of the subsistence basket. -/
noncomputable def reproductionGap (p b : ι → ℝ) (y : ℝ) : ℝ :=
  p ⬝ᵥ b - y

/-- The agent can reproduce when income covers the basket. -/
def CanReproduce (p b : ι → ℝ) (y : ℝ) : Prop := p ⬝ᵥ b ≤ y

theorem canReproduce_iff_gap_nonpos {p b : ι → ℝ} {y : ℝ} :
    CanReproduce p b y ↔ reproductionGap p b y ≤ 0 := by
  unfold CanReproduce reproductionGap
  constructor <;> intro h <;> linarith

theorem gap_antitone_income {p b : ι → ℝ} {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) :
    reproductionGap p b y₂ ≤ reproductionGap p b y₁ := by
  unfold reproductionGap
  linarith

/-- Wage needed to buy the basket from `L` hours of labour. -/
noncomputable def reproductionWage (p b : ι → ℝ) (L : ℝ) : ℝ :=
  (p ⬝ᵥ b) / L

/-- A wage below the reproduction wage leaves a full-time worker short. -/
theorem below_reproductionWage {p b : ι → ℝ} {L w : ℝ} (hL : 0 < L)
    (h : w < reproductionWage p b L) : w * L < p ⬝ᵥ b := by
  unfold reproductionWage at h
  rw [lt_div_iff₀ hL] at h
  exact h

/-- Hours of labour needed to reach subsistence, given capital income `K`. -/
noncomputable def labourNeeded (p b : ι → ℝ) (w K : ℝ) : ℝ :=
  (p ⬝ᵥ b - K) / w

/-- Reproduction is equivalent to the required hours not exceeding the
endowment. -/
theorem canReproduce_iff_labourNeeded_le {p b : ι → ℝ} {w K L : ℝ} (hw : 0 < w) :
    CanReproduce p b (w * L + K) ↔ labourNeeded p b w K ≤ L := by
  unfold CanReproduce labourNeeded
  rw [div_le_iff₀ hw]
  constructor <;> intro h <;> nlinarith

/-- Capital income substitutes for labour in reproduction. -/
theorem labourNeeded_antitone {p b : ι → ℝ} {w : ℝ} (hw : 0 < w) {K₁ K₂ : ℝ}
    (h : K₁ ≤ K₂) : labourNeeded p b w K₂ ≤ labourNeeded p b w K₁ := by
  unfold labourNeeded
  exact div_le_div_of_nonneg_right (by linarith) hw.le

/-- **Bottom pressure.** If income at full endowment is below subsistence,
the hours needed exceed the endowment. -/
theorem reproduction_pressure {p b : ι → ℝ} {w K L : ℝ} (hw : 0 < w)
    (h : w * L + K < p ⬝ᵥ b) : L < labourNeeded p b w K := by
  unfold labourNeeded
  rw [lt_div_iff₀ hw]
  nlinarith

/-! ## Stone–Geary demand -/

/-- Stone–Geary demand: buy the basket `b`, then spend the surplus in value
shares `α`.  Below subsistence, buy a rationed multiple of `b`. -/
noncomputable def lesDemand (p b α : ι → ℝ) (y : ℝ) : ι → ℝ :=
  fun c =>
    if p ⬝ᵥ b ≤ y then
      b c + (y - p ⬝ᵥ b) * α c / p c
    else
      (y / (p ⬝ᵥ b)) * b c

/-- Above subsistence, demand exhausts income. -/
theorem lesDemand_budget_surplus {p b α : ι → ℝ} {y : ℝ}
    (hpc : ∀ c, p c ≠ 0) (hα : ∑ c, α c = 1) (h : p ⬝ᵥ b ≤ y) :
    p ⬝ᵥ lesDemand p b α y = y := by
  have hd : lesDemand p b α y
      = b + fun c => (y - p ⬝ᵥ b) * α c / p c := by
    ext c
    unfold lesDemand
    rw [if_pos h]
    simp only [Pi.add_apply]
  rw [hd, dotProduct_add]
  have hsecond : p ⬝ᵥ (fun c => (y - p ⬝ᵥ b) * α c / p c)
      = (y - p ⬝ᵥ b) * (∑ c, α c) := by
    unfold dotProduct
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    change p c * ((y - p ⬝ᵥ b) * α c / p c) = (y - p ⬝ᵥ b) * α c
    rw [mul_div_cancel₀ _ (hpc c)]
  rw [hsecond, hα]
  ring

/-- Below subsistence, demand also exhausts income, but on a scaled-down
basket. -/
theorem lesDemand_budget_rationed {p b α : ι → ℝ} {y : ℝ}
    (hB : p ⬝ᵥ b ≠ 0) (h : y < p ⬝ᵥ b) :
    p ⬝ᵥ lesDemand p b α y = y := by
  have hd : lesDemand p b α y = (y / (p ⬝ᵥ b)) • b := by
    ext c
    unfold lesDemand
    rw [if_neg (by linarith : ¬ p ⬝ᵥ b ≤ y)]
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd, dotProduct_smul]
  exact div_mul_cancel₀ y hB

/-- Above subsistence every commodity is at least the required basket. -/
theorem lesDemand_ge_floor {p b α : ι → ℝ} {y : ℝ} {c : ι}
    (hpc : 0 < p c) (hα0 : 0 ≤ α c) (h : p ⬝ᵥ b ≤ y) :
    b c ≤ lesDemand p b α y c := by
  unfold lesDemand
  rw [if_pos h]
  have hterm : 0 ≤ (y - p ⬝ᵥ b) * α c / p c :=
    div_nonneg (mul_nonneg (by linarith) hα0) hpc.le
  linarith

/-- Below subsistence the agent is rationed below the basket. -/
theorem lesDemand_le_floor_of_rationed {p b α : ι → ℝ} {y : ℝ} {c : ι}
    (hb : 0 ≤ b c) (hB : 0 < p ⬝ᵥ b) (h : y < p ⬝ᵥ b) :
    lesDemand p b α y c ≤ b c := by
  unfold lesDemand
  rw [if_neg (by linarith : ¬ p ⬝ᵥ b ≤ y)]
  have hr : y / (p ⬝ᵥ b) ≤ 1 := (div_le_one hB).mpr h.le
  have := mul_le_mul_of_nonneg_right hr hb
  simpa using this

/-- Saving: income not spent on consumption. -/
noncomputable def saving (p c : ι → ℝ) (y : ℝ) : ℝ := y - p ⬝ᵥ c

/-- Investment is only possible out of the surplus above subsistence. -/
def SavingFeasible (p b : ι → ℝ) (y s : ℝ) : Prop :=
  0 ≤ s ∧ s ≤ y - p ⬝ᵥ b

/-- Consumption funded by `y − s`. -/
noncomputable def consumption (p b α : ι → ℝ) (y s : ℝ) : ι → ℝ :=
  lesDemand p b α (y - s)

/-- A feasible saving leaves enough income to buy the basket. -/
theorem savingFeasible_le_subsistence {p b : ι → ℝ} {y s : ℝ}
    (h : SavingFeasible p b y s) : p ⬝ᵥ b ≤ y - s := by
  linarith [h.2]

/-- **Spending adds up.** Expenditure plus saving equals income. -/
theorem expenditure_add_saving {p b α : ι → ℝ} {y s : ℝ}
    (hpc : ∀ c, p c ≠ 0) (hB : p ⬝ᵥ b ≠ 0) (hα : ∑ c, α c = 1) :
    p ⬝ᵥ consumption p b α y s + s = y := by
  unfold consumption
  by_cases h : p ⬝ᵥ b ≤ y - s
  · rw [lesDemand_budget_surplus hpc hα h]
    ring
  · have hlt : y - s < p ⬝ᵥ b := lt_of_not_ge h
    rw [lesDemand_budget_rationed hB hlt]
    ring

/-! ## The population's income and demand -/

namespace Population

variable (P : Population κ) (w π : ℝ)

/-- Wage income of the population. -/
def wageIncome : ℝ := w * P.totalLabour

/-- Capital income of the population. -/
def capitalIncome : ℝ := π * P.totalCapital

theorem totalIncome_eq_wage_add_capital :
    P.totalIncome w π = P.wageIncome w + P.capitalIncome π := by
  rw [P.totalIncome_eq]
  rfl

/-- Aggregate consumption demand. -/
noncomputable def aggregateConsumption (p b α : ι → ℝ) (s : κ → ℝ) : ι → ℝ :=
  ∑ i, consumption p b α (P.income w π i) (s i)

/-- **Aggregate Walras' law.** Expenditure plus saving equals total income. -/
theorem aggregate_budget (p b α : ι → ℝ) (s : κ → ℝ)
    (hpc : ∀ c, p c ≠ 0) (hB : p ⬝ᵥ b ≠ 0) (hα : ∑ c, α c = 1) :
    (∑ i, p ⬝ᵥ consumption p b α (P.income w π i) (s i)) + (∑ i, s i)
      = P.totalIncome w π := by
  rw [← Finset.sum_add_distrib]
  have hper : ∀ i, p ⬝ᵥ consumption p b α (P.income w π i) (s i) + s i
      = P.income w π i := fun i => expenditure_add_saving hpc hB hα
  simp_rw [hper]
  unfold totalIncome
  rfl

/-- A pure worker reproduces iff the wage covers the basket. -/
theorem pure_worker_canReproduce {p b : ι → ℝ} {i : κ} (hK : P.capital i = 0) :
    CanReproduce p b (P.income w π i) ↔ w * P.labour i ≥ p ⬝ᵥ b := by
  unfold CanReproduce
  simp [Population.income, hK]

/-- **The wage floor for reproduction.** A pure worker reproduces iff the
wage is at least the subsistence cost per hour. -/
theorem pure_worker_wage_floor {p b : ι → ℝ} {i : κ} (hK : P.capital i = 0)
    (hL : 0 < P.labour i) :
    CanReproduce p b (P.income w π i) ↔ reproductionWage p b (P.labour i) ≤ w := by
  rw [pure_worker_canReproduce P w π hK]
  unfold reproductionWage
  rw [div_le_iff₀ hL]

/-- **A worker who cannot reproduce is rationed below the basket.** -/
theorem cannot_reproduce_rationed {p b α : ι → ℝ} {i : κ} {c : ι}
    (hb : 0 ≤ b c) (hB : 0 < p ⬝ᵥ b)
    (h : P.income w π i < p ⬝ᵥ b) :
    lesDemand p b α (P.income w π i) c ≤ b c :=
  lesDemand_le_floor_of_rationed hb hB h

end Population

end LeanMarx
