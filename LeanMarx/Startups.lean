import LeanMarx.Selection

set_option linter.unusedSectionVars false

/-!
# Startups

Investors found new producers.  An investor commits a fraction `θ i` of their
capital to a startup with expected rate `r i`; the startup is subject to the
same survival rule as any producer, `M' > M`:

* it succeeds when `0 < r i`, returning `c * (1 + r i)` on committed capital
  `c = θ i * M i`;
* it fails when `r i ≤ 0`, and the committed capital is lost.

So one startup round changes investor wealth by `+ c r i` on success and
`- c` on failure.  With success probability `p i`, the expected gain is
`c * (p i * (1 + r i) - 1)`, and the startup is worth founding exactly when
the expected gross return exceeds one, `1 < p i * (1 + r i)`.

Entry of startups into the producer population is modelled by adjoining a new
producer index set: `entryCapital` and `entryRate` live on `φ ⊕ ψ`, so old
producers and new startups are subject to one exit rule.  With entry, exit
and growth the model has the classical firm-dynamics ingredients; a stationary
power law still needs a stochastic distribution of startup outcomes.
-/

namespace LeanMarx

open Finset Sum

variable {κ φ ψ : Type*} [Fintype κ] [Fintype φ] [Fintype ψ]
  [DecidableEq κ] [DecidableEq φ] [DecidableEq ψ]

/-! ## A single startup -/

/-- A startup: capital committed to a new producer and its expected rate. -/
structure Startup where
  capital : ℝ
  rate : ℝ

/-- Value of the startup after one period.  It survives only if `M' > M`,
i.e. `0 < rate`; otherwise it is bankrupt and worth nothing. -/
noncomputable def Startup.value (s : Startup) : ℝ :=
  if 0 < s.rate then s.capital * (1 + s.rate) else 0

theorem Startup.value_of_survives {s : Startup} (h : 0 < s.rate) :
    s.value = s.capital * (1 + s.rate) := by
  simp [Startup.value, h]

theorem Startup.value_of_bankrupt {s : Startup} (h : s.rate ≤ 0) : s.value = 0 := by
  simp [Startup.value, not_lt.mpr h]

/-- **A startup survives exactly when `M' > M`.** -/
theorem Startup.survives_iff {s : Startup} (h : 0 < s.capital) :
    s.capital < s.value ↔ 0 < s.rate := by
  by_cases hr : 0 < s.rate
  · rw [Startup.value_of_survives hr]
    constructor <;> intro _ <;> nlinarith
  · have hb : s.rate ≤ 0 := le_of_not_gt hr
    rw [Startup.value_of_bankrupt hb]
    exact ⟨fun hlt => by linarith, fun hpos => absurd hpos hr⟩

/-- The gain on a successful startup. -/
theorem Startup.gain_of_survives {s : Startup} (h : 0 < s.rate) :
    s.value - s.capital = s.capital * s.rate := by
  rw [Startup.value_of_survives h]
  ring

/-- The loss on a failed startup. -/
theorem Startup.loss_of_bankrupt {s : Startup} (h : s.rate ≤ 0) :
    s.value - s.capital = -s.capital := by
  rw [Startup.value_of_bankrupt h]
  ring

/-! ## An investor's startup round -/

/-- Capital committed to the startup, as a fraction of wealth. -/
noncomputable def committed (M : κ → ℝ) (θ : κ → ℝ) (i : κ) : ℝ := θ i * M i

/-- Investor wealth after one startup round: uncommitted capital plus the
startup's value. -/
noncomputable def wealthAfterStartup (M θ r : κ → ℝ) (i : κ) : ℝ :=
  M i - committed M θ i + (Startup.mk (committed M θ i) (r i)).value

/-- On success the investor keeps the committed capital and its return. -/
theorem wealthAfterStartup_of_survives {M θ r : κ → ℝ} {i : κ} (h : 0 < r i) :
    wealthAfterStartup M θ r i = M i + committed M θ i * r i := by
  simp [wealthAfterStartup, committed, Startup.value, h]
  ring

/-- On failure the committed capital is lost. -/
theorem wealthAfterStartup_of_bankrupt {M θ r : κ → ℝ} {i : κ} (h : r i ≤ 0) :
    wealthAfterStartup M θ r i = M i - committed M θ i := by
  simp [wealthAfterStartup, committed, Startup.value, not_lt.mpr h]

/-- Expected wealth from one startup round, with success probability `p`. -/
noncomputable def expectedStartupWealth (M θ r p : κ → ℝ) (i : κ) : ℝ :=
  p i * (M i + committed M θ i * r i)
    + (1 - p i) * (M i - committed M θ i)

theorem expectedStartupWealth_eq (M θ r p : κ → ℝ) (i : κ) :
    expectedStartupWealth M θ r p i
      = M i + committed M θ i * (p i * r i - (1 - p i)) := by
  unfold expectedStartupWealth committed
  ring

/-- A startup is worth founding when its expected gross return beats the
capital committed. -/
def WorthStarting (p r : ℝ) : Prop := 1 < p * (1 + r)

/-- **Entry condition.** The expected gain from a startup is positive exactly
when `p (1 + r) > 1`. -/
theorem expectedStartupWealth_gain_iff {M θ r p : κ → ℝ} {i : κ}
    (h : 0 < committed M θ i) :
    0 < expectedStartupWealth M θ r p i - M i ↔ WorthStarting (p i) (r i) := by
  rw [expectedStartupWealth_eq, WorthStarting]
  constructor <;> intro h' <;> nlinarith

/-! ## Entry into the producer population -/

/-- Capital after entry: old producers `φ` and startups `ψ` adjoined. -/
noncomputable def entryCapital (K : φ → ℝ) (A : ψ → ℝ) : (φ ⊕ ψ) → ℝ :=
  Sum.elim K A

/-- Profit rates after entry. -/
noncomputable def entryRate (q : φ → ℝ) (r : ψ → ℝ) : (φ ⊕ ψ) → ℝ :=
  Sum.elim q r

theorem sum_entryCapital (K : φ → ℝ) (A : ψ → ℝ) :
    ∑ p : φ ⊕ ψ, entryCapital K A p = (∑ p, K p) + (∑ s, A s) := by
  rw [Fintype.sum_sum_type]
  rfl

/-- A startup with a nonpositive rate is bankrupt on entry. -/
theorem entry_startup_bankrupt {q : φ → ℝ} {r : ψ → ℝ} {K : φ → ℝ}
    {A : ψ → ℝ} {s : ψ} (h : r s ≤ 0) :
    exitStep (entryRate q r) (entryCapital K A) (Sum.inr s) = 0 := by
  apply exitStep_of_bankrupt
  simpa [entryRate] using h

/-- A startup with a positive rate enters and grows. -/
theorem entry_startup_survives {q : φ → ℝ} {r : ψ → ℝ} {K : φ → ℝ}
    {A : ψ → ℝ} {s : ψ} (h : 0 < r s) :
    exitStep (entryRate q r) (entryCapital K A) (Sum.inr s) = A s * (1 + r s) := by
  have hr : 0 < entryRate q r (Sum.inr s) := by simpa [entryRate] using h
  rw [exitStep_of_survivor hr]
  simp [entryCapital, entryRate]

/-- After entry and exit, every producer still holding capital has a positive
rate — startups included. -/
theorem entry_survivors_pos_rate {q : φ → ℝ} {r : ψ → ℝ} {K : φ → ℝ}
    {A : ψ → ℝ} {p : φ ⊕ ψ} (h : 0 < exitStep (entryRate q r) (entryCapital K A) p) :
    0 < entryRate q r p :=
  exitStep_pos_rate h

end LeanMarx
