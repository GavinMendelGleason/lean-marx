import LeanMarx.Price

/-!
# When do prices correspond to labour values?

The **transformation problem**: prices of production generally differ from
labour values. This file states exactly what is required for the two to be
proportional.

Write `v = l (I − A)⁻¹` for labour values and let prices solve the Sraffa
system with profit rate `r ≠ 0`. Then prices are proportional to labour
values **if and only if** labour values are proportional to direct labour
inputs, which in turn is equivalent to the direct labour vector being a
left eigenvector of the input–output matrix (equal organic composition of
capital). At `r = 0` prices are always proportional to values, so the
criterion bites only when there is profit.

Nothing here assumes a sign or irreducibility condition on `A`; those would
strengthen the conclusions (e.g. positivity) but are not needed for the
equivalence.
-/

namespace LeanMarx

open Matrix

/-- `u` and `v` are proportional when `u = c • v` for some nonzero real
`c`. No positivity is required. -/
def Proportional {ι : Type*} (u v : ι → ℝ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ u = c • v

/-- Cancel a nonzero scalar in a vector equation. -/
theorem smul_eq_iff_eq_smul {ι : Type*} {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    {u w : ι → ℝ} : a • u = b • w ↔ u = (b / a) • w := by
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [div_mul_eq_mul_div₀, eq_div_iff ha]
    linarith
  · rintro rfl
    rw [smul_smul, mul_div_cancel₀ b ha]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Economy

variable (E : Economy ι)
variable {p : ι → ℝ} {r w : ℝ}

/-- The price matrix `M(r) = I − (1 + r) A`, whose invertibility makes the
price system solvable at profit rate `r`. -/
noncomputable def priceMatrix (r : ℝ) : Matrix ι ι ℝ := 1 - (1 + r) • E.A

/-- Dotting the price system with the price matrix gives
`p (I − (1+r) A) = (1+r) w l`. -/
theorem price_mul_priceMatrix {p : ι → ℝ} {r w : ℝ}
    (hp : E.IsPriceSystem p r w) :
    p ᵥ* E.priceMatrix r = ((1 + r) * w) • E.l := by
  have hp' : p = (1 + r) • (p ᵥ* E.A) + ((1 + r) * w) • E.l := by
    rw [IsPriceSystem] at hp
    nth_rewrite 1 [hp]
    rw [smul_add, smul_smul]
  calc p ᵥ* E.priceMatrix r
      = p - (1 + r) • (p ᵥ* E.A) := by
        rw [priceMatrix, vecMul_sub, vecMul_one, vecMul_smul]
    _ = ((1 + r) * w) • E.l := by
        nth_rewrite 1 [hp']
        rw [add_sub_cancel_left]

/-- **Labour correspondence criterion.**

Suppose labour values satisfy the value equation `v (I − A) = l`, prices solve
the Sraffa system with `r ≠ 0`, and `I − (1+r) A` is invertible. Then

`p ∝ v  ↔  v ∝ l`.

The left side is the labour correspondence; the right side says labour
values are proportional to direct labour, i.e. every sector has the same
organic composition of capital. -/
theorem price_proportional_value_iff {p : ι → ℝ} {r w : ℝ}
    (hvl : E.value ᵥ* E.leontief = E.l)
    (hvne : E.value ≠ 0)
    (hM : IsUnit (E.priceMatrix r).det)
    (hp : E.IsPriceSystem p r w)
    (hr : r ≠ 0) (hw : w ≠ 0) (hr1 : 1 + r ≠ 0) :
    Proportional p E.value ↔ Proportional E.value E.l := by
  constructor
  · rintro ⟨k, hk, hkp⟩
    -- `k v M = (1+r) w l` and `v M = -r v + (1+r) l`
    have hA : E.value ᵥ* E.A = E.value - E.l := by
      ext i
      have hi := congrFun hvl i
      rw [leontief, vecMul_sub, vecMul_one] at hi
      simp only [Pi.sub_apply] at hi ⊢
      linarith
    have hMv : E.value ᵥ* E.priceMatrix r
        = (-r) • E.value + (1 + r) • E.l := by
      rw [priceMatrix, vecMul_sub, vecMul_one, vecMul_smul, hA]
      module
    have hkM : k • (E.value ᵥ* E.priceMatrix r) = ((1 + r) * w) • E.l := by
      rw [← smul_vecMul, ← hkp, E.price_mul_priceMatrix hp]
    have h3 : (k * (-r)) • E.value
        = (((1 + r) * w) - k * (1 + r)) • E.l := by
      have h := congrArg (fun z => k • z) hMv
      rw [hkM, smul_add, smul_smul, smul_smul] at h
      rw [sub_smul, eq_sub_iff_add_eq]
      exact h.symm
    have ha : k * (-r) ≠ 0 := mul_ne_zero hk (neg_ne_zero.mpr hr)
    have hb : ((1 + r) * w) - k * (1 + r) ≠ 0 := by
      intro hb0
      rw [hb0, zero_smul] at h3
      have : E.value = 0 := by
        rcases smul_eq_zero.mp h3 with h' | h'
        · exact absurd h' ha
        · exact h'
      exact hvne this
    exact ⟨_, div_ne_zero hb ha, (smul_eq_iff_eq_smul ha _).mp h3⟩
  · rintro ⟨c, hc, hcv⟩
    -- `v = c l`, hence `l (I − A) = c⁻¹ l` and `l A = (1 − c⁻¹) l`
    have hle : E.l ᵥ* E.leontief = (1 / c) • E.l := by
      have h1 : c • (E.l ᵥ* E.leontief) = E.l := by
        have h := hvl
        rw [hcv, smul_vecMul] at h
        exact h
      exact (smul_eq_iff_eq_smul hc 1).mp (by simpa using h1)
    have hμ : E.l ᵥ* E.A = (1 - c⁻¹) • E.l := by
      have h := hle
      rw [leontief, vecMul_sub, vecMul_one] at h
      ext i
      have hi := congrFun h i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, one_div] at hi ⊢
      linarith
    set lam : ℝ := 1 - (1 + r) * (1 - c⁻¹) with hlamdef
    have hlM : E.l ᵥ* E.priceMatrix r = lam • E.l := by
      rw [priceMatrix, vecMul_sub, vecMul_one, vecMul_smul, hμ, smul_smul, hlamdef,
        sub_smul, one_smul]
    have hlam : lam ≠ 0 := by
      intro h0
      have hzero : E.l ᵥ* E.priceMatrix r = 0 := by rw [hlM, h0, zero_smul]
      have hl0 : E.l = 0 := by
        have hinj := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det (E.priceMatrix r)).mpr hM)
        have := hinj (by rw [hzero, zero_vecMul] : E.l ᵥ* E.priceMatrix r = 0 ᵥ* E.priceMatrix r)
        exact this
      have : E.value = 0 := by rw [hcv, hl0, smul_zero]
      exact hvne this
    have hpeq : p = ((1 + r) * w / lam) • E.l := by
      refine (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det (E.priceMatrix r)).mpr hM)) ?_
      change p ᵥ* E.priceMatrix r = (((1 + r) * w / lam) • E.l) ᵥ* E.priceMatrix r
      rw [smul_vecMul, E.price_mul_priceMatrix hp, hlM, smul_smul]
      congr 1
      rw [div_mul_cancel₀ _ hlam]
    have hl : E.l = (1 / c) • E.value :=
      (smul_eq_iff_eq_smul hc 1).mp (by simpa using hcv.symm)
    refine ⟨((1 + r) * w / lam) * (1 / c), ?_, ?_⟩
    · exact mul_ne_zero (div_ne_zero (mul_ne_zero hr1 hw) hlam) (div_ne_zero one_ne_zero hc)
    · rw [hpeq, hl, smul_smul]

/-- **Equal organic composition.** Labour values are proportional to direct
labour inputs exactly when the direct labour vector is a left eigenvector
of the input–output matrix. -/
theorem value_proportional_labour_iff_leftEigen (h : E.Productive) :
    Proportional E.value E.l ↔ ∃ μ : ℝ, E.l ᵥ* E.A = μ • E.l := by
  constructor
  · rintro ⟨c, hc, hcv⟩
    have hle : E.l ᵥ* E.leontief = (1 / c) • E.l := by
      have h1 : c • (E.l ᵥ* E.leontief) = E.l := by
        have h := E.value_leontief h
        rw [hcv, smul_vecMul] at h
        exact h
      exact (smul_eq_iff_eq_smul hc 1).mp (by simpa using h1)
    refine ⟨1 - c⁻¹, ?_⟩
    have h' := hle
    rw [leontief, vecMul_sub, vecMul_one] at h'
    ext i
    have hi := congrFun h' i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, one_div] at hi ⊢
    linarith
  · rintro ⟨μ, hμ⟩
    by_cases hμ1 : μ = 1
    · -- `l (I − A) = 0`, so `l = 0` and `v = 0`
      subst hμ1
      have hl0 : E.l = 0 := by
        have hinj := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det E.leontief).mpr h)
        have hzero : E.l ᵥ* E.leontief = 0 := by
          rw [leontief, vecMul_sub, vecMul_one, hμ, one_smul, sub_self]
        have := hinj (by rw [hzero, zero_vecMul] :
          E.l ᵥ* E.leontief = 0 ᵥ* E.leontief)
        exact this
      refine ⟨1, one_ne_zero, ?_⟩
      show E.value = 1 • E.l
      rw [hl0, smul_zero, value, hl0, zero_vecMul]
    · refine ⟨1 / (1 - μ), div_ne_zero one_ne_zero (sub_ne_zero.mpr (Ne.symm hμ1)), ?_⟩
      -- both sides solve `w (I − A) = l`, and `vecMul` by `I − A` is injective
      refine (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det E.leontief).mpr h)) ?_
      change E.value ᵥ* E.leontief = ((1 / (1 - μ)) • E.l) ᵥ* E.leontief
      rw [E.value_leontief h, smul_vecMul, leontief, vecMul_sub, vecMul_one, hμ]
      rw [show E.l - μ • E.l = (1 - μ) • E.l by rw [sub_smul, one_smul],
        smul_smul, div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hμ1)), one_smul]

end Economy

end LeanMarx
