import Mathlib

set_option linter.unusedSectionVars false

/-!
# Input–output production tables

An economy is a **production table** over a finite set of commodities `ι` and
a finite set of activities `j`:

* `A : Matrix ι j ℝ` — the **use** matrix: `A i k` units of commodity `i`
  consumed per unit of activity `k`;
* `B : Matrix ι j ℝ` — the **make** matrix: `B i k` units of commodity `i`
  produced per unit of activity `k`.  Several rows of a column may be
  nonzero, so joint production is allowed;
* `l : j → ℝ` — labour input per unit of activity `k`, a row of the input
  side of the table.

No sign or productivity condition is built in; theorems take what they need.

The table fixes the **net-output operator** `N = B − A`.  Activity `x`
yields net output `N *ᵥ x` and employment `l ⬝ᵥ x`.  Labour values are the
vectors `v` with `v N = l`.

With joint production `N` is rectangular and need not be invertible.  That is
the substantive point the single-product model hides:

* `ValuesExist` (`N` has a left inverse, i.e. is injective) says every labour
  input vector has a labour value;
* `ValuesUnique` (`N` has a right inverse, i.e. is surjective) says a labour
  value is unique when it exists.

Both hold exactly when `N` is invertible.  When they fail, the table does not
determine labour values, and no pricing convention can repair that.
-/

namespace LeanMarx

open Matrix

variable {ι j : Type*} [Fintype ι] [Fintype j] [DecidableEq ι] [DecidableEq j]

/-- `N` has a left inverse, equivalently the map `x ↦ N *ᵥ x` is injective,
equivalently `v ↦ v ᵥ* N` is surjective. -/
def HasLeftInverse (N : Matrix ι j ℝ) : Prop :=
  ∃ C : Matrix j ι ℝ, C * N = 1

/-- `N` has a right inverse, equivalently the map `x ↦ N *ᵥ x` is surjective,
equivalently `v ↦ v ᵥ* N` is injective. -/
def HasRightInverse (N : Matrix ι j ℝ) : Prop :=
  ∃ D : Matrix j ι ℝ, N * D = 1

/-- **Existence.** A left inverse gives a labour value for every labour input
vector. -/
theorem exists_labourValue {N : Matrix ι j ℝ} (h : HasLeftInverse N)
    (l : j → ℝ) : ∃ v : ι → ℝ, v ᵥ* N = l := by
  obtain ⟨C, hC⟩ := h
  exact ⟨l ᵥ* C, by rw [vecMul_vecMul, hC, vecMul_one]⟩

/-- **Uniqueness.** A right inverse makes the labour value unique when it
exists. -/
theorem unique_labourValue {N : Matrix ι j ℝ} (h : HasRightInverse N)
    {l : j → ℝ} {v₁ v₂ : ι → ℝ} (h₁ : v₁ ᵥ* N = l) (h₂ : v₂ ᵥ* N = l) :
    v₁ = v₂ := by
  obtain ⟨D, hD⟩ := h
  have h0 : (v₁ - v₂) ᵥ* N = 0 := by rw [sub_vecMul, h₁, h₂, sub_self]
  have hEq : v₁ - v₂ = (v₁ - v₂) ᵥ* (N * D) := by rw [hD, vecMul_one]
  rw [← vecMul_vecMul, h0, zero_vecMul] at hEq
  exact sub_eq_zero.mp hEq

/-- A production table with commodities `ι` and activities `j`. -/
structure ProductionTable (ι j : Type*) [Fintype ι] [Fintype j] where
  /-- Use matrix: commodity inputs per unit of activity. -/
  A : Matrix ι j ℝ
  /-- Make matrix: commodity outputs per unit of activity. -/
  B : Matrix ι j ℝ
  /-- Labour input per unit of activity. -/
  l : j → ℝ

namespace ProductionTable

variable (T : ProductionTable ι j)

/-- The net-output operator `B − A`. -/
def netOp : Matrix ι j ℝ := T.B - T.A

/-- Net output of activity vector `x`. -/
def netOutput (x : j → ℝ) : ι → ℝ := T.netOp *ᵥ x

/-- Employment of activity vector `x`. -/
def employment (x : j → ℝ) : ℝ := T.l ⬝ᵥ x

/-- `v` is a vector of labour values when it accounts for the labour embodied
in net output: `v (B − A) = l`. -/
def IsLabourValue (v : ι → ℝ) : Prop := v ᵥ* T.netOp = T.l

/-- Every labour input vector has a labour value: `B − A` has a left inverse. -/
def ValuesExist : Prop := HasLeftInverse T.netOp

/-- A labour value is unique when it exists: `B − A` has a right inverse. -/
def ValuesUnique : Prop := HasRightInverse T.netOp

/-- The table determines labour values: existence and uniqueness.  For a
square net-output operator this is exactly invertibility. -/
def DeterminesValues : Prop := T.ValuesExist ∧ T.ValuesUnique

/-- Labour values read off a left inverse of the net-output operator. -/
noncomputable def labourValue (C : Matrix j ι ℝ) : ι → ℝ := T.l ᵥ* C

theorem labourValue_isLabourValue {C : Matrix j ι ℝ} (hC : C * T.netOp = 1) :
    T.IsLabourValue (T.labourValue C) := by
  unfold IsLabourValue labourValue
  rw [vecMul_vecMul, hC, vecMul_one]

/-- **The table determines labour values.** Existence and uniqueness together
give a unique labour-value vector. -/
theorem existsUnique_labourValue (h : T.DeterminesValues) :
    ∃! v : ι → ℝ, T.IsLabourValue v := by
  obtain ⟨hE, hU⟩ := h
  obtain ⟨v, hv⟩ := exists_labourValue hE T.l
  refine ⟨v, hv, ?_⟩
  intro w hw
  exact unique_labourValue hU hw hv

/-- Labour embodied in net output equals employment. -/
theorem value_netOutput {v : ι → ℝ} (hv : T.IsLabourValue v) (x : j → ℝ) :
    v ⬝ᵥ T.netOutput x = T.employment x := by
  rw [netOutput, employment, dotProduct_mulVec, hv]

end ProductionTable

end LeanMarx
