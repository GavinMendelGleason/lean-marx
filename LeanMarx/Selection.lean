import LeanMarx.Expectations

set_option linter.unusedSectionVars false

/-!
# Producers, investment and bankruptcy

A **producer** is a column of the production table making one indexed
commodity.  Several producers may make the same commodity, so an industry can
have more than one possible technique.  Investors fund producers (by expected
profit rates, as in `LeanMarx.Expectations`), and a producer survives only if
its capital reproduces itself:

`M p  →  M' p = M p * (1 + r p)`,

and it survives only when `M' p > M p`; if `M' p ≤ M p` it goes bankrupt.

Formalised:

* `survives_iff`: `M' > M` exactly when `r p > 0`;
* `bankrupt_iff`: `M' ≤ M` exactly when `r p ≤ 0`;
* `tendsto_capitalPath_zero`: a producer with `-1 < r p < 0` loses capital
  geometrically, so it vanishes;
* `exitStep`: one period of growth with bankruptcy (nonpositive-rate
  producers exit at zero capital);
* `tendsto_share_selected`: a producer with a strictly dominant rate takes
  the whole capital share, so selection concentrates surviving capital.

Exit is what the earlier models lacked: multiplicative growth plus bankruptcy
is the classical ingredient list for a Pareto firm-size distribution.  But a
power law needs entry of new producers and stochastic growth on top of exit;
deterministic selection alone drives the distribution to a point mass.
-/

namespace LeanMarx

open Filter Finset Matrix
open scoped Topology

variable {ι φ : Type*} [Fintype ι] [Fintype φ] [DecidableEq ι] [DecidableEq φ]

/-- A production table whose columns are single-product producers. -/
structure ProducerTable (ι φ : Type*) [Fintype ι] [Fintype φ] where
  /-- Commodity inputs per unit of the producer's activity. -/
  input : Matrix ι φ ℝ
  /-- The commodity each producer makes. -/
  output : φ → ι
  /-- Labour input per unit of activity. -/
  labour : φ → ℝ

namespace ProducerTable

variable (T : ProducerTable ι φ)

/-- The producer table as a general production table: producer `p` makes one
unit of `T.output p`. -/
def toTable : ProductionTable ι φ :=
  { A := T.input
    B := fun i p => if i = T.output p then 1 else 0
    l := T.labour }

/-- The producers making commodity `c`. -/
def producersOf (c : ι) : Finset φ :=
  Finset.univ.filter fun p => T.output p = c

theorem mem_producersOf_self (p : φ) : p ∈ T.producersOf (T.output p) := by
  simp [producersOf]

/-- The net output of producer `p` is one unit of its commodity less its
inputs. -/
theorem toTable_netOp_apply (i : ι) (p : φ) :
    T.toTable.netOp i p = (if i = T.output p then 1 else 0) - T.input i p := by
  rfl

end ProducerTable

/-! ## Growth and bankruptcy -/

variable {r K : φ → ℝ}

/-- Capital after one period of production: `M' = M (1 + r)`. -/
noncomputable def capitalStep (r K : φ → ℝ) : φ → ℝ := fun p => K p * (1 + r p)

/-- **Survival is `M' > M`.** A producer survives exactly when its capital
grows. -/
theorem survives_iff {p : φ} (hK : 0 < K p) :
    K p < capitalStep r K p ↔ 0 < r p := by
  unfold capitalStep
  constructor <;> intro h <;> nlinarith

/-- **Bankruptcy is `M' ≤ M`.** A producer that does not grow fails. -/
theorem bankrupt_iff {p : φ} (hK : 0 < K p) :
    capitalStep r K p ≤ K p ↔ r p ≤ 0 := by
  unfold capitalStep
  constructor <;> intro h <;> nlinarith

/-- Capital along the multiplicative path. -/
noncomputable def capitalPath (r K : φ → ℝ) (t : ℕ) : φ → ℝ :=
  fun p => K p * (1 + r p) ^ t

/-- The capital path is the multiplicative circuit with rates `r`. -/
theorem capitalPath_eq_wealthAt (r K : φ → ℝ) (t : ℕ) :
    capitalPath r K t = wealthAt r K t := by
  ext p
  simp [capitalPath, wealthAt, mul_comm]

/-- **A failing producer vanishes.** With `-1 < r p < 0` its capital decays
geometrically to zero. -/
theorem tendsto_capitalPath_zero {r K : φ → ℝ} {p : φ}
    (hlo : -1 < r p) (hhi : r p < 0) :
    Tendsto (fun t => capitalPath r K t p) atTop (𝓝 0) := by
  have hr0 : 0 ≤ 1 + r p := by linarith
  have hr1 : 1 + r p < 1 := by linarith
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (K p)
  simpa [capitalPath, mul_comm] using h

/-- **One period with bankruptcy.** A nonpositive-rate producer exits with
zero capital; a positive-rate producer grows. -/
noncomputable def exitStep (r K : φ → ℝ) : φ → ℝ :=
  fun p => if 0 < r p then K p * (1 + r p) else 0

theorem exitStep_of_bankrupt {r K : φ → ℝ} {p : φ} (h : r p ≤ 0) :
    exitStep r K p = 0 := by
  simp [exitStep, not_lt.mpr h]

theorem exitStep_of_survivor {r K : φ → ℝ} {p : φ} (h : 0 < r p) :
    exitStep r K p = K p * (1 + r p) := by
  simp [exitStep, h]

/-- After bankruptcy, every producer holding capital has a positive rate. -/
theorem exitStep_pos_rate {r K : φ → ℝ} {p : φ} (h : 0 < exitStep r K p) :
    0 < r p := by
  by_contra hle
  have hzero : exitStep r K p = 0 := exitStep_of_bankrupt (le_of_not_gt hle)
  linarith

/-- **Selection.** If one producer's rate strictly dominates every other, its
capital share tends to one: the others are selected out. -/
theorem tendsto_share_selected (r K : φ → ℝ) (q : φ)
    (h0 : ∀ p, 0 ≤ 1 + r p) (hq : ∀ p, p ≠ q → 1 + r p < 1 + r q)
    (hqpos : 0 < 1 + r q) (hKq : 0 < K q) :
    Tendsto (fun t => share (capitalPath r K t) q) atTop (𝓝 1) := by
  have h := tendsto_share_dominant r K q h0 hq hqpos hKq
  have hiter : (fun t : ℕ => share (capitalPath r K t) q)
      = fun t : ℕ => share (wealthAt r K t) q := by
    funext t
    rw [capitalPath_eq_wealthAt]
  rw [hiter]
  exact h

end LeanMarx
