import LeanMarx.Price

/-!
# Income distribution with mixed worker–capitalist agents

Every agent may both work (earning the wage) and own capital (earning
profit), so an agent is a *mixture* of worker and capitalist. With
endowments `labour i` and `capital i`, wage rate `w` and profit rate `π`:

* income: `y i = w * labour i + π * capital i`;
* income share: `s i = y i / Σ y`.

The main structural result is that each income share is a **convex
combination** of the agent's labour share and capital share, with weights
equal to the economy-wide wage share and profit share:

`s i = ω * (labour i / L) + (1 - ω) * (capital i / K)`.

Consequences formalised below:

* if all agents have the same capital-per-worker ratio, the wage share
  does not change anyone's relative income (`incomeShare = labourShare`);
* a pure worker's share is `ω` times their labour share;
* the Gini coefficient of the income distribution is at most the
  wage-share/profit-share weighted average of the Gini coefficients of the
  two endowments, because mixing can only offset differences.
-/

namespace LeanMarx

open Finset

variable {κ : Type*} [Fintype κ]

/-- A population of agents, each with a labour endowment (hours) and a
capital endowment. -/
structure Population (κ : Type*) [Fintype κ] where
  /-- Labour endowment in hours. -/
  labour : κ → ℝ
  /-- Capital endowment. -/
  capital : κ → ℝ

namespace Population

variable (P : Population κ)

/-- Total labour endowment. -/
def totalLabour : ℝ := ∑ i, P.labour i

/-- Total capital endowment. -/
def totalCapital : ℝ := ∑ i, P.capital i

/-- Income of each agent at wage rate `w` and profit rate `π`. -/
def income (w π : ℝ) : κ → ℝ := fun i => w * P.labour i + π * P.capital i

/-- Total income of the population. -/
def totalIncome (w π : ℝ) : ℝ := ∑ i, P.income w π i

/-- Income share of an agent. -/
noncomputable def incomeShare (w π : ℝ) (i : κ) : ℝ :=
  P.income w π i / P.totalIncome w π

/-- Labour endowment share of an agent. -/
noncomputable def labourShare (i : κ) : ℝ := P.labour i / P.totalLabour

/-- Capital endowment share of an agent. -/
noncomputable def capitalShare (i : κ) : ℝ := P.capital i / P.totalCapital

/-- The economy-wide wage share of income. -/
noncomputable def wageShareOfIncome (w π : ℝ) : ℝ :=
  w * P.totalLabour / P.totalIncome w π

/-- The economy-wide profit share of income. -/
noncomputable def profitShareOfIncome (w π : ℝ) : ℝ :=
  π * P.totalCapital / P.totalIncome w π

/-- Total income is the wage bill plus total profit. -/
theorem totalIncome_eq (w π : ℝ) :
    P.totalIncome w π = w * P.totalLabour + π * P.totalCapital := by
  unfold totalIncome income totalLabour totalCapital
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Each agent is a mixture.** An agent's income share is the wage share
times their labour share plus the profit share times their capital share. -/
theorem incomeShare_eq_mixture (w π : ℝ) (i : κ)
    (hY : P.totalIncome w π ≠ 0) (hL : P.totalLabour ≠ 0)
    (hK : P.totalCapital ≠ 0) :
    P.incomeShare w π i
      = P.wageShareOfIncome w π * P.labourShare i
        + P.profitShareOfIncome w π * P.capitalShare i := by
  have hY' : w * P.totalLabour + π * P.totalCapital ≠ 0 := by
    rw [← P.totalIncome_eq]; exact hY
  unfold incomeShare wageShareOfIncome profitShareOfIncome labourShare capitalShare income
  rw [P.totalIncome_eq]
  field_simp

/-- The wage share and the profit share of income add to one. -/
theorem wageShare_add_profitShare (w π : ℝ) (hY : P.totalIncome w π ≠ 0) :
    P.wageShareOfIncome w π + P.profitShareOfIncome w π = 1 := by
  unfold wageShareOfIncome profitShareOfIncome
  rw [← add_div, ← P.totalIncome_eq]
  exact div_self hY

/-- The wage share of income is nonnegative for a nonnegative wage and
nonnegative labour endowments. -/
theorem wageShareOfIncome_nonneg (w π : ℝ) (hw : 0 ≤ w)
    (hl : ∀ i, 0 ≤ P.labour i) (hY : 0 < P.totalIncome w π) :
    0 ≤ P.wageShareOfIncome w π := by
  unfold wageShareOfIncome totalLabour
  exact div_nonneg (mul_nonneg hw (Finset.sum_nonneg fun i _ => hl i)) hY.le

/-- The profit share of income is nonnegative for a nonnegative profit rate
and nonnegative capital endowments. -/
theorem profitShareOfIncome_nonneg (w π : ℝ) (hπ : 0 ≤ π)
    (hk : ∀ i, 0 ≤ P.capital i) (hY : 0 < P.totalIncome w π) :
    0 ≤ P.profitShareOfIncome w π := by
  unfold profitShareOfIncome totalCapital
  exact div_nonneg (mul_nonneg hπ (Finset.sum_nonneg fun i _ => hk i)) hY.le

/-- Income shares sum to one. -/
theorem sum_incomeShare (w π : ℝ) (hY : P.totalIncome w π ≠ 0) :
    ∑ i, P.incomeShare w π i = 1 := by
  unfold incomeShare
  rw [← Finset.sum_div]
  exact div_self hY

/-- Income shares are nonnegative when wages, profits and endowments are. -/
theorem incomeShare_nonneg (w π : ℝ) (hw : 0 ≤ w) (hπ : 0 ≤ π)
    (hl : ∀ i, 0 ≤ P.labour i) (hk : ∀ i, 0 ≤ P.capital i)
    (hY : 0 < P.totalIncome w π) (i : κ) : 0 ≤ P.incomeShare w π i := by
  unfold incomeShare income
  exact div_nonneg
    (add_nonneg (mul_nonneg hw (hl i)) (mul_nonneg hπ (hk i))) hY.le

/-- Income shares are at most one when wages, profits and endowments are. -/
theorem incomeShare_le_one (w π : ℝ) (hw : 0 ≤ w) (hπ : 0 ≤ π)
    (hl : ∀ i, 0 ≤ P.labour i) (hk : ∀ i, 0 ≤ P.capital i)
    (hY : 0 < P.totalIncome w π) (i : κ) : P.incomeShare w π i ≤ 1 := by
  unfold incomeShare
  rw [div_le_one hY]
  unfold totalIncome
  refine Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ i)
  exact add_nonneg (mul_nonneg hw (hl j)) (mul_nonneg hπ (hk j))

/-- **Equal mixtures: no distributional effect from the class split.** If
every agent holds capital in the same proportion to labour, income shares
equal labour shares whatever the wage and profit rates. -/
theorem incomeShare_eq_labourShare_of_proportional {w π ρ : ℝ}
    (hρ : ∀ i, P.capital i = ρ * P.labour i)
    (hY : P.totalIncome w π ≠ 0) (i : κ) :
    P.incomeShare w π i = P.labourShare i := by
  have hsum : P.totalCapital = ρ * P.totalLabour := by
    unfold totalCapital totalLabour
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hρ i
  have hden : w * P.totalLabour + π * (ρ * P.totalLabour) ≠ 0 := by
    have h := hY
    rw [P.totalIncome_eq, hsum] at h
    exact h
  have hden' : (w + π * ρ) * P.totalLabour ≠ 0 := by
    have h := hden
    rw [show w * P.totalLabour + π * (ρ * P.totalLabour)
        = (w + π * ρ) * P.totalLabour by ring] at h
    exact h
  have ha : w + π * ρ ≠ 0 := left_ne_zero_of_mul hden'
  unfold incomeShare labourShare income
  rw [hρ i, P.totalIncome_eq, hsum]
  rw [show w * P.labour i + π * (ρ * P.labour i) = (w + π * ρ) * P.labour i by ring]
  rw [show w * P.totalLabour + π * (ρ * P.totalLabour) = (w + π * ρ) * P.totalLabour by ring]
  exact mul_div_mul_left _ _ ha

/-- **Pure worker.** An agent owning no capital receives the wage share
times their labour share. -/
theorem incomeShare_of_pure_worker (w π : ℝ) (i : κ)
    (hY : P.totalIncome w π ≠ 0) (hL : P.totalLabour ≠ 0)
    (hK : P.totalCapital ≠ 0) (hk : P.capital i = 0) :
    P.incomeShare w π i = P.wageShareOfIncome w π * P.labourShare i := by
  rw [P.incomeShare_eq_mixture w π i hY hL hK]
  unfold capitalShare
  rw [hk, zero_div, mul_zero, add_zero]

end Population

/-- The Gini coefficient of a vector, with mean normalisation:
`Σᵢ Σⱼ |xᵢ − xⱼ| / (2 n Σᵢ xᵢ)`. -/
noncomputable def gini (x : κ → ℝ) : ℝ :=
  (∑ i, ∑ j, |x i - x j|) / (2 * (Fintype.card κ : ℝ) * ∑ i, x i)

/-- **Mixing cannot increase inequality.** The Gini coefficient of a convex
combination of two distributions with unit mass is at most the same convex
combination of their Gini coefficients: differences between the two
components can cancel, never reinforce. -/
theorem gini_mixture_le [Nonempty κ] {ω : ℝ} (hω : 0 ≤ ω) (hω1 : 0 ≤ 1 - ω)
    {lam kap : κ → ℝ} (hlam : ∑ i, lam i = 1) (hkap : ∑ i, kap i = 1) :
    gini (fun i => ω * lam i + (1 - ω) * kap i)
      ≤ ω * gini lam + (1 - ω) * gini kap := by
  have hy : ∑ i, (ω * lam i + (1 - ω) * kap i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hlam, hkap]
    ring
  have hcard : (0 : ℝ) < 2 * (Fintype.card κ : ℝ) := by
    have : 0 < Fintype.card κ := Fintype.card_pos
    positivity
  have hC : (∑ i, ∑ j,
        |(ω * lam i + (1 - ω) * kap i) - (ω * lam j + (1 - ω) * kap j)|)
      ≤ ω * (∑ i, ∑ j, |lam i - lam j|)
        + (1 - ω) * (∑ i, ∑ j, |kap i - kap j|) := by
    calc (∑ i, ∑ j,
            |(ω * lam i + (1 - ω) * kap i) - (ω * lam j + (1 - ω) * kap j)|)
        ≤ ∑ i, ∑ j, (ω * |lam i - lam j| + (1 - ω) * |kap i - kap j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [show (ω * lam i + (1 - ω) * kap i) - (ω * lam j + (1 - ω) * kap j)
              = ω * (lam i - lam j) + (1 - ω) * (kap i - kap j) by ring]
          calc |ω * (lam i - lam j) + (1 - ω) * (kap i - kap j)|
              ≤ |ω * (lam i - lam j)| + |(1 - ω) * (kap i - kap j)| := abs_add_le _ _
            _ = ω * |lam i - lam j| + (1 - ω) * |kap i - kap j| := by
                rw [abs_mul, abs_mul, abs_of_nonneg hω, abs_of_nonneg hω1]
      _ = ω * (∑ i, ∑ j, |lam i - lam j|)
            + (1 - ω) * (∑ i, ∑ j, |kap i - kap j|) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc gini (fun i => ω * lam i + (1 - ω) * kap i)
      = (∑ i, ∑ j,
          |(ω * lam i + (1 - ω) * kap i) - (ω * lam j + (1 - ω) * kap j)|)
          / (2 * (Fintype.card κ : ℝ)) := by
        unfold gini
        rw [hy, mul_one]
    _ ≤ (ω * (∑ i, ∑ j, |lam i - lam j|)
            + (1 - ω) * (∑ i, ∑ j, |kap i - kap j|))
          / (2 * (Fintype.card κ : ℝ)) := div_le_div_of_nonneg_right hC hcard.le
    _ = ω * ((∑ i, ∑ j, |lam i - lam j|) / (2 * (Fintype.card κ : ℝ)))
          + (1 - ω) * ((∑ i, ∑ j, |kap i - kap j|) / (2 * (Fintype.card κ : ℝ))) := by
        field_simp
    _ = ω * gini lam + (1 - ω) * gini kap := by
        unfold gini
        rw [hlam, hkap, mul_one]

end LeanMarx
