import LeanMarx.Investment

set_option linter.unusedSectionVars false

/-!
# Banking, credit creation and debt

A minimal accounting core for a monetary production economy.

* A **balance sheet** has assets, liabilities and equity `A − L`.  Lending is
  a swap of assets and liabilities: a loan of `L` creates a deposit of `L`, so
  equity is unchanged (`equity_createLoan`).  Repayment destroys both
  (`equity_repayLoan`).  A write-off removes the asset but not the liability,
  so equity falls by the loss (`equity_writeOff`).
* A **firm** holds capital and deposits against debt.  It is insolvent when
  debt exceeds assets (`Firm.insolvent_iff`).
* **Investment** is funded by retained earnings plus credit, and credit is
  bounded by a limit (`Funding.investment_le_retained_add_capacity`).  With a
  zero credit limit the funded investment is exactly retained earnings
  (`investment_of_no_credit`) — the reduction to the real model.
* A bank's **credit capacity** is equity times a leverage ratio
  (`creditCapacity`), which is the comparative parameter for the financial
  sector.

Money is endogenous: deposits are created by lending and destroyed by
repayment.  The module does not model reserves, the central bank or deposit
insurance; those are later layers.
-/

namespace LeanMarx

open Finset

/-! ## Balance sheets -/

/-- A balance sheet: assets and liabilities. -/
structure BalanceSheet where
  assets : ℝ
  liabilities : ℝ

namespace BalanceSheet

/-- Equity is assets less liabilities. -/
def equity (b : BalanceSheet) : ℝ := b.assets - b.liabilities

/-- The balance-sheet identity. -/
theorem assets_eq_liabilities_add_equity (b : BalanceSheet) :
    b.assets = b.liabilities + b.equity := by
  unfold equity
  ring

/-- **Credit creation.** A loan of `L` creates a deposit of `L`, expanding
both sides. -/
def createLoan (b : BalanceSheet) (L : ℝ) : BalanceSheet :=
  { assets := b.assets + L, liabilities := b.liabilities + L }

/-- Credit creation is equity-neutral. -/
theorem equity_createLoan (b : BalanceSheet) (L : ℝ) :
    (createLoan b L).equity = b.equity := by
  unfold createLoan equity
  ring

/-- **Repayment** destroys the deposit and the loan. -/
def repayLoan (b : BalanceSheet) (L : ℝ) : BalanceSheet :=
  { assets := b.assets - L, liabilities := b.liabilities - L }

/-- Repayment is equity-neutral. -/
theorem equity_repayLoan (b : BalanceSheet) (L : ℝ) :
    (repayLoan b L).equity = b.equity := by
  unfold repayLoan equity
  ring

/-- **A write-off** removes the asset but not the liability. -/
def writeOff (b : BalanceSheet) (L : ℝ) : BalanceSheet :=
  { assets := b.assets - L, liabilities := b.liabilities }

/-- A write-off reduces equity by the loss. -/
theorem equity_writeOff (b : BalanceSheet) (L : ℝ) :
    (writeOff b L).equity = b.equity - L := by
  unfold writeOff equity
  ring

end BalanceSheet

/-! ## Firm funding, debt and insolvency -/

/-- A firm's real capital, liquid deposits and debt. -/
structure Firm where
  capital : ℝ
  deposits : ℝ
  debt : ℝ

namespace Firm

/-- Assets are capital plus deposits. -/
def assets (f : Firm) : ℝ := f.capital + f.deposits

/-- Equity is assets less debt. -/
def equity (f : Firm) : ℝ := f.assets - f.debt

/-- Insolvency: negative equity. -/
def insolvent (f : Firm) : Prop := f.equity < 0

/-- Insolvency is debt exceeding assets. -/
theorem insolvent_iff (f : Firm) : f.insolvent ↔ f.assets < f.debt := by
  unfold insolvent equity
  constructor <;> intro h <;> linarith

end Firm

/-- Investment funding: retained earnings, a credit limit and a desired
investment. -/
structure Funding where
  retained : ℝ
  creditLimit : ℝ
  desired : ℝ

namespace Funding

/-- The borrowing requirement: the part of desired investment not covered by
retained earnings. -/
def borrowing (f : Funding) : ℝ := max 0 (f.desired - f.retained)

/-- Actual credit: the borrowing requirement capped by the credit limit. -/
def credit (f : Funding) : ℝ := min f.borrowing f.creditLimit

/-- Funded investment. -/
def investment (f : Funding) : ℝ := f.retained + f.credit

/-- **Credit is bounded by the limit.** -/
theorem credit_le_limit (f : Funding) : f.credit ≤ f.creditLimit := by
  unfold credit
  exact min_le_right _ _

/-- **Investment never exceeds retained earnings plus the credit limit.** -/
theorem investment_le_retained_add_capacity (f : Funding) :
    f.investment ≤ f.retained + f.creditLimit := by
  unfold investment
  linarith [f.credit_le_limit]

/-- **Zero credit recovers the real model:** investment is retained earnings. -/
theorem investment_of_no_credit (f : Funding) (h : f.creditLimit = 0) :
    f.investment = f.retained := by
  unfold investment credit
  have hb : 0 ≤ f.borrowing := le_max_left _ _
  rw [h, min_eq_right hb]
  ring

/-- A higher credit limit cannot lower funded investment. -/
theorem credit_mono_limit (f : Funding) {L₁ L₂ : ℝ} (h : L₁ ≤ L₂) :
    min f.borrowing L₁ ≤ min f.borrowing L₂ :=
  min_le_min_left f.borrowing h

end Funding

/-- One period of debt: interest accrues and repayment reduces the principal. -/
noncomputable def debtStep (debt interest repayment : ℝ) : ℝ :=
  (1 + interest) * debt - repayment

/-- Debt falls when repayment exceeds the interest charge. -/
theorem debtStep_lt_self {d i r : ℝ} (h : i * d < r) : debtStep d i r < d := by
  unfold debtStep
  nlinarith

/-- A bank's credit capacity from equity and a leverage ratio. -/
noncomputable def creditCapacity (equity leverage : ℝ) : ℝ := leverage * equity

/-- Higher leverage raises credit capacity. -/
theorem creditCapacity_mono_leverage {e l₁ l₂ : ℝ} (he : 0 ≤ e) (h : l₁ ≤ l₂) :
    creditCapacity e l₁ ≤ creditCapacity e l₂ := by
  unfold creditCapacity
  exact mul_le_mul_of_nonneg_right h he

/-- A bank's equity after a loan loss. -/
noncomputable def bankEquityAfterLoss (equity loss : ℝ) : ℝ := equity - loss

/-- A loss exceeding equity makes the bank insolvent. -/
theorem bank_insolvent_of_loss {e l : ℝ} (h : e < l) : bankEquityAfterLoss e l < 0 := by
  unfold bankEquityAfterLoss
  linarith

end LeanMarx
