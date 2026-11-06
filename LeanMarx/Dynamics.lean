import LeanMarx.Circuit

set_option linter.unusedSectionVars false

/-!
# Time

Two discrete-time structures, both single-period elsewhere.

* A **balanced-growth path** of activities for a fixed production table:
  `x (t+1) = (1+g) x t`.  Activity, net output, employment and the money
  value of net output grow at `1+g`; labour values and cost prices are
  stationary, so value accounting holds at every date.

* A **capital circuit** with a per-investor profit rate:
  `w (t+1) i = (1+π i) w t i`, solved by `w t i = (1+π i)^t w0 i`.

The circuit has a sharp distributional consequence.  Equal rates preserve
every share and the Gini coefficient at every date.  If one investor's rate
strictly dominates, that investor's share tends to one: deterministic
differential accumulation concentrates wealth into a point mass.  A
non-degenerate power law therefore cannot come from the circuit alone; it
needs stochastic shocks, a reflecting barrier or a reset.
-/

namespace LeanMarx

open Filter Finset Matrix
open scoped Topology

/-! ## Balanced growth of the production table -/

/-- A balanced-growth activity path. -/
structure BalancedPath (j : Type*) where
  /-- Activity vector at each date. -/
  x : ℕ → j → ℝ
  /-- Growth factor minus one. -/
  g : ℝ
  /-- One step multiplies every activity by `1 + g`. -/
  step : ∀ t, x (t + 1) = (1 + g) • x t

namespace BalancedPath

variable {j : Type*} (P : BalancedPath j)

/-- The closed form of a balanced path. -/
theorem x_eq (t : ℕ) : P.x t = (1 + P.g) ^ t • P.x 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [P.step, ih, smul_smul, pow_succ, mul_comm]

end BalancedPath

namespace ProductionTable

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]
variable (T : ProductionTable ι j) (P : BalancedPath j)

/-- Employment grows at the path's rate. -/
theorem employment_eq (t : ℕ) :
    T.employment (P.x t) = (1 + P.g) ^ t * T.employment (P.x 0) := by
  rw [P.x_eq]
  simp [employment, dotProduct_smul]

/-- Net output grows at the path's rate. -/
theorem netOutput_eq (t : ℕ) :
    T.netOutput (P.x t) = (1 + P.g) ^ t • T.netOutput (P.x 0) := by
  rw [P.x_eq t]
  simp only [netOutput, mulVec_smul]

/-- The money value of net output grows at the path's rate. -/
theorem price_netOutput_eq (p : ι → ℝ) (t : ℕ) :
    p ⬝ᵥ T.netOutput (P.x t)
      = (1 + P.g) ^ t * (p ⬝ᵥ T.netOutput (P.x 0)) := by
  rw [netOutput_eq T P, dotProduct_smul, smul_eq_mul]

end ProductionTable

/-! ## The capital circuit -/

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Wealth of investor `i` after `t` turns with per-investor profit rates. -/
noncomputable def wealthAt (π : κ → ℝ) (w0 : κ → ℝ) (t : ℕ) (i : κ) : ℝ :=
  (1 + π i) ^ t * w0 i

/-- The circuit law: one turn multiplies investor `i`'s wealth by `1 + π i`. -/
def IsCircuit (π : κ → ℝ) (w : ℕ → κ → ℝ) : Prop :=
  ∀ t i, w (t + 1) i = (1 + π i) * w t i

theorem wealthAt_isCircuit (π : κ → ℝ) (w0 : κ → ℝ) :
    IsCircuit π (wealthAt π w0) := by
  intro t i
  unfold wealthAt
  rw [pow_succ]
  ring

/-- The circuit law with an initial condition has a unique solution. -/
theorem circuit_unique {π : κ → ℝ} {w : ℕ → κ → ℝ} {w0 : κ → ℝ}
    (h0 : w 0 = w0) (h : IsCircuit π w) (t : ℕ) :
    w t = wealthAt π w0 t := by
  induction t with
  | zero =>
      ext i
      simpa [wealthAt] using congrFun h0 i
  | succ t ih =>
      ext i
      rw [h t i, ih]
      unfold wealthAt
      rw [pow_succ]
      ring

/-- Equal rates reduce the path to a single scaling. -/
theorem wealthAt_uniform_eq (π : ℝ) (w0 : κ → ℝ) (t : ℕ) :
    wealthAt (fun _ : κ => π) w0 t = (1 + π) ^ t • w0 := by
  ext i
  simp [wealthAt]

/-- **Equal rates preserve every share at every date.** -/
theorem share_wealthAt_uniform {π : ℝ} (h : 1 + π ≠ 0) (w0 : κ → ℝ)
    (hS : ∑ i, w0 i ≠ 0) (t : ℕ) (i : κ) :
    share (wealthAt (fun _ : κ => π) w0 t) i = share w0 i := by
  rw [wealthAt_uniform_eq]
  exact share_smul ((1 + π) ^ t) (pow_ne_zero t h) w0 hS i

/-- **Equal rates preserve the Gini coefficient at every date.** -/
theorem gini_wealthAt_uniform {π : ℝ} (h : 0 < 1 + π) (w0 : κ → ℝ) (t : ℕ) :
    gini (wealthAt (fun _ : κ => π) w0 t) = gini w0 := by
  rw [wealthAt_uniform_eq]
  exact gini_smul (pow_pos h t) w0

/-- Total capital grows at the uniform rate. -/
theorem sum_wealthAt_uniform (π : ℝ) (w0 : κ → ℝ) (t : ℕ) :
    ∑ i, wealthAt (fun _ : κ => π) w0 t i = (1 + π) ^ t * ∑ i, w0 i := by
  rw [wealthAt_uniform_eq]
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- Each share can be written with the dominant-rate factor cancelled. -/
theorem share_wealthAt_eq (π : κ → ℝ) (w0 : κ → ℝ) (j : κ)
    (hj : 1 + π j ≠ 0) (t : ℕ) :
    share (wealthAt π w0 t) j
      = w0 j / (w0 j + ∑ i ∈ Finset.univ.erase j,
          ((1 + π i) / (1 + π j)) ^ t * w0 i) := by
  have hterm : ∀ i : κ, (1 + π i) ^ t * w0 i
      = (1 + π j) ^ t * (((1 + π i) / (1 + π j)) ^ t * w0 i) := by
    intro i
    calc (1 + π i) ^ t * w0 i
        = ((1 + π j) * ((1 + π i) / (1 + π j))) ^ t * w0 i := by
          rw [mul_div_cancel₀ (1 + π i) hj]
      _ = ((1 + π j) ^ t * ((1 + π i) / (1 + π j)) ^ t) * w0 i := by
          rw [mul_pow]
      _ = (1 + π j) ^ t * (((1 + π i) / (1 + π j)) ^ t * w0 i) := by
          ring
  have hden : ∑ i, wealthAt π w0 t i
      = (1 + π j) ^ t * (w0 j + ∑ i ∈ Finset.univ.erase j,
          ((1 + π i) / (1 + π j)) ^ t * w0 i) := by
    simp only [wealthAt]
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ j)]
    rw [Finset.sum_insert (by simp)]
    have hsplit : ∑ i ∈ Finset.univ.erase j, (1 + π i) ^ t * w0 i
        = (1 + π j) ^ t * ∑ i ∈ Finset.univ.erase j,
            ((1 + π i) / (1 + π j)) ^ t * w0 i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hterm i
    rw [hsplit, mul_add]
  unfold share
  rw [hden]
  simp only [wealthAt]
  rw [mul_div_mul_left _ _ (pow_ne_zero t hj)]

/-- **Differential rates concentrate.** If one investor's rate strictly
dominates every other and the initial wealth is positive, that investor's
share tends to one and the asymptotic distribution is a point mass. -/
theorem tendsto_share_dominant (π : κ → ℝ) (w0 : κ → ℝ) (j : κ)
    (h0 : ∀ i, 0 ≤ 1 + π i) (hj : ∀ i, i ≠ j → 1 + π i < 1 + π j)
    (hjpos : 0 < 1 + π j) (hwj : 0 < w0 j) :
    Tendsto (fun t => share (wealthAt π w0 t) j) atTop (𝓝 1) := by
  have hjne : 1 + π j ≠ 0 := hjpos.ne'
  set S : ℕ → ℝ := fun t => ∑ i ∈ Finset.univ.erase j,
      ((1 + π i) / (1 + π j)) ^ t * w0 i with hSdef
  have hS : Tendsto S atTop (𝓝 0) := by
    rw [hSdef]
    have h := tendsto_finsetSum (s := Finset.univ.erase j) (x := atTop)
      (f := fun i (t : ℕ) => ((1 + π i) / (1 + π j)) ^ t * w0 i)
      (a := fun _ : κ => (0 : ℝ)) (by
        intro i hi
        have hi' : i ≠ j := (Finset.mem_erase.mp hi).1
        have hlt : (1 + π i) / (1 + π j) < 1 := by
          rw [div_lt_one hjpos]
          exact hj i hi'
        have hge : 0 ≤ (1 + π i) / (1 + π j) := div_nonneg (h0 i) hjpos.le
        have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hge hlt
        simpa using hp.mul_const (w0 i))
    simpa using h
  have hden : Tendsto (fun t => w0 j + S t) atTop (𝓝 (w0 j + 0)) :=
    tendsto_const_nhds.add hS
  have hnum : Tendsto (fun _ : ℕ => w0 j) atTop (𝓝 (w0 j)) := tendsto_const_nhds
  have hlim : Tendsto (fun t => w0 j / (w0 j + S t)) atTop (𝓝 1) := by
    have h := hnum.div hden (by simpa using hwj.ne')
    have hfun2 : ((fun _ : ℕ => w0 j) / (fun t => w0 j + S t))
        = fun t => w0 j / (w0 j + S t) := by
      funext t
      rfl
    rw [hfun2] at h
    simpa only [add_zero, div_self hwj.ne'] using h
  have hfun : (fun t => share (wealthAt π w0 t) j)
      = fun t => w0 j / (w0 j + S t) := by
    funext t
    rw [share_wealthAt_eq π w0 j hjne t, ← congrFun hSdef t]
  rw [hfun]
  exact hlim

/-- **Linear-over-linear asymptotics.** `(a + t c) / (b + t Δ)` tends to
`c / Δ` for positive `b` and `Δ`.  This covers both the multiplicative circuit
with a constant surplus and entry allocated by a fixed rule. -/
theorem tendsto_lin_ratio (a c : ℝ) {b Δ : ℝ} (hb : 0 < b) (hΔ : 0 < Δ) :
    Tendsto (fun t : ℕ => (a + t * c) / (b + t * Δ)) atTop (𝓝 (c / Δ)) := by
  have h1 : Tendsto (fun t : ℕ => a / t + c) atTop (𝓝 c) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) a).add_const c
  have h2 : Tendsto (fun t : ℕ => b / t + Δ) atTop (𝓝 Δ) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) b).add_const Δ
  have h3 : Tendsto (fun t : ℕ => (a / t + c) / (b / t + Δ)) atTop (𝓝 (c / Δ)) := by
    have h := h1.div h2 (by simpa using hΔ.ne')
    have hfun2 : ((fun t : ℕ => a / t + c) / (fun t : ℕ => b / t + Δ))
        = fun t : ℕ => (a / t + c) / (b / t + Δ) := by
      funext t
      rfl
    rw [hfun2] at h
    simpa using h
  have heq : ∀ᶠ t : ℕ in atTop,
      (a / t + c) / (b / t + Δ) = (a + t * c) / (b + t * Δ) := by
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
