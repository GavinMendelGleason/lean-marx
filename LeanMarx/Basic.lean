import Mathlib

/-!
# Linear single-product economies

A single-product economy over a finite set of sectors `ι`.

* `A i j` is the quantity of commodity `j` consumed in producing one unit of
  commodity `i` (the input–output matrix).
* `l i` is the direct labour expended per unit of gross output of `i`.

The structure carries no sign or productivity assumptions: a theorem that
needs them takes them as hypotheses, which keeps visible exactly which
economic conditions each result rests on.

The central object is the vector of **labour values** `v = l (I − A)⁻¹`,
whose coordinates are the total labour embodied in one unit of each
commodity.
-/

namespace LeanMarx

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A single-product linear economy. -/
structure Economy (ι : Type*) [Fintype ι] where
  /-- Input–output matrix: `A i j` units of `j` per unit of `i`. -/
  A : Matrix ι ι ℝ
  /-- Direct labour coefficients: hours per unit of gross output. -/
  l : ι → ℝ

namespace Economy

variable (E : Economy ι)

/-- The Leontief matrix `I − A`. -/
def leontief : Matrix ι ι ℝ := 1 - E.A

/-- The Leontief inverse. -/
noncomputable def leontiefInv : Matrix ι ι ℝ := E.leontief⁻¹

/-- Labour values `v = l (I − A)⁻¹`: total labour embodied in one unit of
each commodity. -/
noncomputable def value : ι → ℝ := E.l ᵥ* E.leontiefInv

/-- The economy is productive when the Leontief matrix is invertible. -/
def Productive : Prop := IsUnit E.leontief.det

/-- **Value equation.** Labour values satisfy `v (I − A) = l`: the labour
embodied in a unit of a commodity equals the direct labour plus the labour
embodied in its material inputs. -/
theorem value_leontief (h : E.Productive) : E.value ᵥ* E.leontief = E.l := by
  rw [value, leontiefInv, vecMul_vecMul]
  rw [Matrix.nonsing_inv_mul (A := E.leontief) (show IsUnit E.leontief.det from h), vecMul_one]

/-- Total employment required by gross output `x`. -/
def employment (x : ι → ℝ) : ℝ := E.l ⬝ᵥ x

/-- Net output: gross output minus material inputs, i.e. `(I − A) x`. -/
def netOutput (x : ι → ℝ) : ι → ℝ := E.leontief *ᵥ x

/-- Net output in labour terms: total labour embodied in the net product.
For productive economies this is total employment. -/
theorem value_netOutput (h : E.Productive) (x : ι → ℝ) :
    E.value ⬝ᵥ E.netOutput x = E.employment x := by
  rw [netOutput, employment, dotProduct_mulVec, E.value_leontief h]

end Economy

end LeanMarx
