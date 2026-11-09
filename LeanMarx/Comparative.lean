import LeanMarx.Banking
import Mathlib.Logic.Function.Iterate

set_option linter.unusedSectionVars false

/-!
# Comparative models: a refinement hierarchy

A richer model is a *conservative extension* of a simpler one when switching
the new feature off projects the richer dynamics onto the simpler dynamics.

Here the real model has capital and a profit rate,

`K' = K (1 + π)`,

and the financed model adds credit,

`K' = K (1 + π) + c`.

With `c = 0` the projection to the real model commutes with the step
(`step_projection_of_no_credit`) and with every finite horizon
(`iterate_projection`).  This is the pattern for the model stack: production →
investment → debt → banking → central banking, each layer with a
switch-off reduction to the layer below, plus comparative statics within the
layer (`credit_increases_capital`, `capital_mono_credit`).
-/

namespace LeanMarx

/-- The real model: capital and a profit rate. -/
structure RealModel where
  capital : ℝ
  profit : ℝ

namespace RealModel

/-- One period of real accumulation. -/
def step (m : RealModel) : RealModel :=
  { capital := m.capital * (1 + m.profit), profit := m.profit }

/-- The `n`-period trajectory. -/
def stepN (m : RealModel) (n : ℕ) : RealModel :=
  Nat.iterate step n m

/-- The successor step of the real trajectory. -/
@[simp] theorem stepN_succ (m : RealModel) (n : ℕ) :
    m.stepN (n + 1) = (m.stepN n).step := by
  rw [stepN, Function.iterate_succ_apply']
  simp [stepN]

end RealModel

/-- The financed model: the real model plus credit. -/
structure FinancedModel where
  capital : ℝ
  profit : ℝ
  credit : ℝ

namespace FinancedModel

/-- Projection onto the real model: drop credit. -/
def toReal (m : FinancedModel) : RealModel :=
  { capital := m.capital, profit := m.profit }

/-- One period with credit-financed investment. -/
def step (m : FinancedModel) : FinancedModel :=
  { capital := m.capital * (1 + m.profit) + m.credit,
    profit := m.profit,
    credit := m.credit }

/-- The `n`-period trajectory. -/
def stepN (m : FinancedModel) (n : ℕ) : FinancedModel :=
  Nat.iterate step n m

/-- The successor step of the financed trajectory. -/
@[simp] theorem stepN_succ (m : FinancedModel) (n : ℕ) :
    m.stepN (n + 1) = (m.stepN n).step := by
  rw [stepN, Function.iterate_succ_apply']
  simp [stepN]

/-- **Reduction.** With zero credit the projection of the financed step is the
real step. -/
theorem step_projection_of_no_credit (m : FinancedModel) (h : m.credit = 0) :
    (m.step).toReal = m.toReal.step := by
  simp [step, toReal, RealModel.step, h]

/-- Credit is preserved by the step. -/
theorem credit_step (m : FinancedModel) : m.step.credit = m.credit := rfl

/-- Zero credit is preserved along the trajectory. -/
theorem credit_stepN (m : FinancedModel) (h : m.credit = 0) (n : ℕ) :
    (m.stepN n).credit = 0 := by
  induction n with
  | zero => simpa [stepN] using h
  | succ n ih =>
      rw [stepN_succ]
      simpa [step] using ih

/-- **Trajectory reduction.** With zero credit the whole financed trajectory
projects onto the real trajectory. -/
theorem iterate_projection (m : FinancedModel) (h : m.credit = 0) (n : ℕ) :
    (m.stepN n).toReal = m.toReal.stepN n := by
  induction n with
  | zero => simp [stepN, RealModel.stepN]
  | succ n ih =>
      have hc : (m.stepN n).credit = 0 := credit_stepN m h n
      rw [stepN_succ, step_projection_of_no_credit (m.stepN n) hc, ih,
        ← RealModel.stepN_succ]

/-- Nonnegative credit does not reduce the capital stock. -/
theorem credit_increases_capital (m : FinancedModel) (h : 0 ≤ m.credit) :
    m.capital * (1 + m.profit) ≤ m.step.capital := by
  unfold step
  linarith

/-- Higher credit gives higher capital. -/
theorem capital_mono_credit (m : FinancedModel) {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    ({ m with credit := c₁ } : FinancedModel).step.capital
      ≤ ({ m with credit := c₂ } : FinancedModel).step.capital := by
  unfold step
  linarith

/-- The no-bank model. -/
def noBank (m : FinancedModel) : FinancedModel := { m with credit := 0 }

/-- Cutting credit recovers the real trajectory. -/
theorem noBank_stepN_eq (m : FinancedModel) (n : ℕ) :
    ((m.noBank).stepN n).toReal = m.toReal.stepN n := by
  exact iterate_projection m.noBank rfl n

end FinancedModel

end LeanMarx
