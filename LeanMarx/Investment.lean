import LeanMarx.Dynamics
import LeanMarx.Surplus

set_option linter.unusedSectionVars false

/-!
# Investment, surplus and preferential attachment

Agents hold capital and invest it in production.  A production period at
total investment `K = Σ I i` yields a surplus `π K` (the rate `π` can be the
table's value rate of profit, `ProductionTable.valueProfitRate`).  The surplus
is distributed by an allocation `s` with `Σ s = 1`, so each agent's capital
moves `M i → M i + ΔM i`:

`investStep π I s w = w + π K * s`.

Two allocation rules matter.

* **Proportional** (`s i = w i / W`) is the scale-invariant case: every
  agent's wealth is multiplied by `1 + πK/W`, so shares and the Gini
  coefficient are unchanged.  Interpreted stochastically, an investor
  receives the next unit of surplus with probability `w i / W`; then the
  *expected* share is exactly preserved (`expected_share_attachment`).
* **Preferential** (`s j > w j / W`) raises the favoured agent's share
  (`preferential_increases_share`).  Winner-takes-all is the extreme case,
  and its capital share tends to one (`tendsto_winnerPath_share`).

The last point is the honest limit of the mechanism: with a fixed finite set
of agents, proportional attachment preserves expected shares (a Pólya urn,
whose limit is Dirichlet), while strictly preferential rules concentrate into
a point mass.  A *power law over agents* needs entry — new agents who take a
share of the surplus (the Yule/Simon mechanism) — not just preferential
allocation among a fixed set.
-/

namespace LeanMarx

open Filter Finset Matrix
open scoped Topology

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## Investment and the surplus -/

/-- Total capital invested by the agents. -/
noncomputable def totalInvestment (I : κ → ℝ) : ℝ := ∑ i, I i

/-- One production period: capital stays with its owner and the surplus
`π * totalInvestment I` is distributed by the allocation `s`. -/
noncomputable def investStep (π : ℝ) (I s : κ → ℝ) (w : κ → ℝ) : κ → ℝ :=
  fun i => w i + π * totalInvestment I * s i

/-! ## Preferential attachment -/

/-- Probability that agent `i` receives the next unit of surplus, proportional
to wealth. -/
noncomputable def attachProb (w : κ → ℝ) (i : κ) : ℝ := w i / ∑ j, w j

theorem attachProb_nonneg {w : κ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < ∑ i, w i) (i : κ) : 0 ≤ attachProb w i :=
  div_nonneg (hw i) hW.le

/-- The attachment probabilities form a probability distribution. -/
theorem sum_attachProb {w : κ → ℝ} (hW : ∑ i, w i ≠ 0) :
    ∑ i, attachProb w i = 1 := by
  unfold attachProb
  rw [← Finset.sum_div, div_self hW]

/-- Preferential: a richer agent is strictly more likely to receive the next
unit of surplus. -/
theorem attachProb_strictMono {w : κ → ℝ} (hW : 0 < ∑ i, w i) {i j : κ}
    (hij : w i < w j) : attachProb w i < attachProb w j := by
  unfold attachProb
  exact div_lt_div_of_pos_right hij hW

/-- **Proportional allocation is scale-invariant.** The surplus distributed
in proportion to wealth multiplies every agent's capital by the same factor. -/
theorem investStep_attach (π : ℝ) (I w : κ → ℝ) (hW : ∑ i, w i ≠ 0) :
    investStep π I (attachProb w) w
      = (1 + π * totalInvestment I / ∑ i, w i) • w := by
  ext i
  unfold investStep totalInvestment attachProb
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Consequently proportional attachment preserves every share. -/
theorem investStep_attach_share (π : ℝ) (I w : κ → ℝ) (hW : ∑ i, w i ≠ 0)
    (hscale : 1 + π * totalInvestment I / ∑ i, w i ≠ 0) (i : κ) :
    share (investStep π I (attachProb w) w) i = share w i := by
  rw [investStep_attach π I w hW]
  exact share_smul _ hscale w hW i

/-- **Random preferential attachment preserves expected shares.** If the next
surplus unit `Δ` goes to `i` with probability `attachProb w i`, the expected
share of `i` after the step is exactly its current share. -/
theorem expected_share_attachment {w : κ → ℝ} (hW : 0 < ∑ i, w i)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (i : κ) :
    (w i + Δ * attachProb w i) / (∑ i, w i + Δ) = attachProb w i := by
  have hWne : ∑ i, w i ≠ 0 := hW.ne'
  have hden : 0 < ∑ i, w i + Δ := by linarith
  unfold attachProb
  field_simp

/-- **Preferential allocation raises the favoured share.** If the allocation
gives agent `j` more than their wealth share, and the surplus is positive,
then the wealth share of `j` strictly increases. -/
theorem preferential_increases_share {w : κ → ℝ} (hW : 0 < ∑ i, w i)
    {Δ : ℝ} (hΔ : 0 < Δ) {s : κ → ℝ} {j : κ}
    (h : w j / (∑ i, w i) < s j) :
    w j / (∑ i, w i) < (w j + Δ * s j) / (∑ i, w i + Δ) := by
  have hden : 0 < ∑ i, w i + Δ := by linarith
  have h' : w j < s j * ∑ i, w i := by
    rw [div_lt_iff₀ hW] at h
    exact h
  rw [div_lt_div_iff₀ hW hden]
  have hmul : w j * Δ < s j * (∑ i, w i) * Δ :=
    mul_lt_mul_of_pos_right h' hΔ
  nlinarith

/-- Winner-takes-all allocation of the surplus. -/
noncomputable def winnerAlloc (j : κ) : κ → ℝ := fun i => if i = j then 1 else 0

@[simp] theorem winnerAlloc_apply_self (j : κ) : winnerAlloc j j = 1 := by
  simp [winnerAlloc]

@[simp] theorem winnerAlloc_apply_of_ne {i j : κ} (h : i ≠ j) :
    winnerAlloc j i = 0 := by
  simp [winnerAlloc, h]

theorem sum_winnerAlloc (j : κ) : ∑ i, winnerAlloc j i = 1 := by
  unfold winnerAlloc
  simp

/-- Winner-takes-all raises the winner's share. -/
theorem winner_share_increases {w : κ → ℝ} (hW : 0 < ∑ i, w i)
    {Δ : ℝ} (hΔ : 0 < Δ) {j : κ} (hj : w j < ∑ i, w i) :
    w j / (∑ i, w i) < (w j + Δ) / (∑ i, w i + Δ) := by
  have hden : 0 < ∑ i, w i + Δ := by linarith
  rw [div_lt_div_iff₀ hW hden]
  nlinarith

/-! ## Winner-takes-all over time -/

/-- Wealth path when the whole surplus `Δ` goes to agent `j` each period. -/
noncomputable def winnerPath (j : κ) (Δ : ℝ) (w0 : κ → ℝ) : ℕ → κ → ℝ :=
  fun t i => w0 i + if i = j then t * Δ else 0

@[simp] theorem winnerPath_apply_self (j : κ) (Δ : ℝ) (w0 : κ → ℝ) (t : ℕ) :
    winnerPath j Δ w0 t j = w0 j + t * Δ := by
  simp [winnerPath]

theorem winnerPath_apply_of_ne {i j : κ} (h : i ≠ j) (Δ : ℝ) (w0 : κ → ℝ)
    (t : ℕ) : winnerPath j Δ w0 t i = w0 i := by
  simp [winnerPath, h]

/-- One step of the winner-takes-all path. -/
theorem winnerPath_succ (j : κ) (Δ : ℝ) (w0 : κ → ℝ) (t : ℕ) :
    winnerPath j Δ w0 (t + 1)
      = fun i => winnerPath j Δ w0 t i + (if i = j then Δ else 0) := by
  ext i
  unfold winnerPath
  push_cast
  by_cases hi : i = j
  · simp [hi]
    ring
  · simp [hi]

/-- Total capital at date `t` under winner-takes-all. -/
theorem sum_winnerPath (j : κ) (Δ : ℝ) (w0 : κ → ℝ) (t : ℕ) :
    ∑ i, winnerPath j Δ w0 t i = ∑ i, w0 i + t * Δ := by
  unfold winnerPath
  rw [Finset.sum_add_distrib]
  have h : ∑ i, (if i = j then t * Δ else 0 : ℝ) = t * Δ := by
    rw [Finset.sum_ite_eq']
    simp
  rw [h]

/-- The winner's capital share at date `t`. -/
theorem winnerPath_share (j : κ) (Δ : ℝ) (w0 : κ → ℝ) (t : ℕ) :
    share (winnerPath j Δ w0 t) j
      = (w0 j + t * Δ) / (∑ i, w0 i + t * Δ) := by
  unfold share
  rw [winnerPath_apply_self, sum_winnerPath]

/-- **Winner-takes-all concentrates.** With a positive surplus, the winner's
capital share tends to one; the asymptotic distribution is a point mass. -/
theorem tendsto_winnerPath_share (j : κ) (Δ : ℝ) (w0 : κ → ℝ) (hΔ : 0 < Δ)
    (hW0 : 0 < ∑ i, w0 i) :
    Tendsto (fun t => share (winnerPath j Δ w0 t) j) atTop (𝓝 1) := by
  simp_rw [winnerPath_share]
  set a : ℝ := w0 j with ha
  set b : ℝ := ∑ i, w0 i with hb
  have hbpos : 0 < b := by rw [hb]; exact hW0
  have h1 : Tendsto (fun t : ℕ => a / t + Δ) atTop (𝓝 Δ) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) a).add_const Δ
  have h2 : Tendsto (fun t : ℕ => b / t + Δ) atTop (𝓝 Δ) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) b).add_const Δ
  have h3 : Tendsto (fun t : ℕ => (a / t + Δ) / (b / t + Δ)) atTop (𝓝 1) := by
    have h := h1.div h2 (by simpa using hΔ.ne')
    have hfun2 : ((fun t : ℕ => a / t + Δ) / (fun t : ℕ => b / t + Δ))
        = fun t : ℕ => (a / t + Δ) / (b / t + Δ) := by
      funext t
      rfl
    rw [hfun2] at h
    simpa only [div_self hΔ.ne'] using h
  have heq : ∀ᶠ t : ℕ in atTop,
      (a / t + Δ) / (b / t + Δ) = (a + t * Δ) / (b + t * Δ) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht0
    have ht : (t : ℝ) ≠ 0 := by exact_mod_cast ht0
    have hbden : b + (t : ℝ) * Δ ≠ 0 := by
      have hpos : 0 < b + (t : ℝ) * Δ := by
        have ht0' : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
        nlinarith
      exact hpos.ne'
    field_simp
  exact h3.congr' heq

end LeanMarx
