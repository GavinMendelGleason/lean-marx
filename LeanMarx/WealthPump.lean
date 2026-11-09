import LeanMarx.FirmSize

set_option linter.unusedSectionVars false

/-!
# The wealth pump: entry, the active sector and the tail

The stationary masses of `LeanMarx.FirmSize` factor as

`π k = e · A k / (1 + e · Σ A)   (k ≥ 1)`,   `π 0 = 1 / (1 + e · Σ A)`,

where `A k = (2/(k+1))^α` is the entry-free profile.  This separates the two
things a "wealth pump" can mean:

* the **shape** of the distribution among active firms: the conditional
  masses `π k / activeShare` are `A k / Σ A`, independent of the entry rate;
  the tail ratio `π(k+1)/π k = ((k+1)/(k+2))^α` is likewise entry-free, so
  the Pareto exponent does not move with entry;
* the **extensive margin and throughput**: the active share
  `Σ_{k≥1} π k = eΣA / (1+eΣA)` and the inflow `π 0 · e = e / (1+eΣA)` are
  strictly increasing in `e`.

So a fall in entry raises the dead/zero-wealth mass `π 0`, lowers the active
sector and lowers the gross flow up the size ladder, while leaving the
Pareto exponent and the conditional distribution among active firms
unchanged.  Measured inequality across the whole population rises (more mass
at zero wealth), but the top wealth share among owners and the tail slope do
not.
-/

namespace LeanMarx

open Finset

/-- Entry-free stationary profile. -/
noncomputable def profile (α : ℝ) (k : ℕ) : ℝ :=
  (2 / ((k : ℝ) + 1)) ^ α

/-- Sum of the profile over the active sizes. -/
noncomputable def profileSum (α : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, profile α (k + 1)

theorem profile_pos (α : ℝ) (hα : 0 < α) (k : ℕ) : 0 < profile α k :=
  Real.rpow_pos_of_pos (by positivity) α

theorem profileSum_pos (α : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N) :
    0 < profileSum α N := by
  unfold profileSum
  exact Finset.sum_pos (fun k _ => profile_pos α hα (k + 1))
    (Finset.nonempty_range_iff.mpr (by omega))

/-- The mass is the entry rate times the entry-free profile. -/
theorem mass_eq_profile (α e : ℝ) (N : ℕ) (hα : 0 < α) {k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) : mass α e N k = e * profile α k := by
  rw [mass_eq α e N hα hk hkN]
  unfold profile
  rfl

/-- The normaliser is `1` plus `e` times the profile sum. -/
theorem norm_eq (α e : ℝ) (N : ℕ) (hα : 0 < α) :
    norm α e N = 1 + e * profileSum α N := by
  unfold norm profileSum
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k + 1 ≤ N := by
    have := Finset.mem_range.mp hk
    omega
  rw [mass_eq α e N hα (by omega) hkN]
  unfold profile
  rfl

/-- The stationary mass in factored form. -/
theorem stationaryMass_eq (α e : ℝ) (N : ℕ) (hα : 0 < α) (k : ℕ) (hk : k ≤ N) :
    stationaryMass α e N k
      = if k = 0 then 1 / (1 + e * profileSum α N)
        else e * profile α k / (1 + e * profileSum α N) := by
  unfold stationaryMass
  rw [norm_eq α e N hα]
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    simp [hk0, mass_eq_profile α e N hα hk1 hk]

/-- **Falling entry raises the dead/zero-wealth mass.** -/
theorem zeroMass_strictAnti (α : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N)
    {e₁ e₂ : ℝ} (he₁ : 0 ≤ e₁) (he : e₁ < e₂) :
    stationaryMass α e₂ N 0 < stationaryMass α e₁ N 0 := by
  rw [stationaryMass_eq α e₂ N hα 0 (Nat.zero_le N),
    stationaryMass_eq α e₁ N hα 0 (Nat.zero_le N)]
  simp only [ite_true]
  have hT : 0 < profileSum α N := profileSum_pos α N hα hN
  have h₁ : 0 < 1 + e₁ * profileSum α N := by nlinarith
  have h₂ : 0 < 1 + e₂ * profileSum α N := by nlinarith
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

/-- Mass of the active firms. -/
noncomputable def activeShare (α e : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, stationaryMass α e N (k + 1)

theorem activeShare_eq (α e : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N) :
    activeShare α e N = e * profileSum α N / (1 + e * profileSum α N) := by
  have hterm : ∀ k ∈ Finset.range N,
      stationaryMass α e N (k + 1)
        = e * profile α (k + 1) / (1 + e * profileSum α N) := by
    intro k hk
    have hkN : k + 1 ≤ N := by
      have := Finset.mem_range.mp hk
      omega
    rw [stationaryMass_eq α e N hα (k + 1) hkN]
    simp
  calc activeShare α e N
      = ∑ k ∈ Finset.range N, e * profile α (k + 1) / (1 + e * profileSum α N) := by
        unfold activeShare
        exact Finset.sum_congr rfl hterm
    _ = (∑ k ∈ Finset.range N, e * profile α (k + 1)) / (1 + e * profileSum α N) := by
        rw [Finset.sum_div]
    _ = e * profileSum α N / (1 + e * profileSum α N) := by
        congr 1
        rw [profileSum, Finset.mul_sum]

/-- **Entry raises the active sector.** -/
theorem activeShare_strictMono (α : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N)
    {e₁ e₂ : ℝ} (he₁ : 0 ≤ e₁) (he : e₁ < e₂) :
    activeShare α e₁ N < activeShare α e₂ N := by
  rw [activeShare_eq α e₁ N hα hN, activeShare_eq α e₂ N hα hN]
  have hT : 0 < profileSum α N := profileSum_pos α N hα hN
  have h₁ : 0 < 1 + e₁ * profileSum α N := by nlinarith
  have h₂ : 0 < 1 + e₂ * profileSum α N := by nlinarith
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

/-- Gross inflow into the firm sector. -/
noncomputable def throughput (α e : ℝ) (N : ℕ) : ℝ :=
  stationaryMass α e N 0 * e

theorem throughput_eq (α e : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N) :
    throughput α e N = e / (1 + e * profileSum α N) := by
  unfold throughput
  rw [stationaryMass_eq α e N hα 0 (Nat.zero_le N)]
  simp
  ring

/-- **Entry raises the throughput of the ladder.** -/
theorem throughput_strictMono (α : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N)
    {e₁ e₂ : ℝ} (he₁ : 0 ≤ e₁) (he : e₁ < e₂) :
    throughput α e₁ N < throughput α e₂ N := by
  rw [throughput_eq α e₁ N hα hN, throughput_eq α e₂ N hα hN]
  have hT : 0 < profileSum α N := profileSum_pos α N hα hN
  have h₁ : 0 < 1 + e₁ * profileSum α N := by nlinarith
  have h₂ : 0 < 1 + e₂ * profileSum α N := by nlinarith
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

/-- **The conditional distribution among active firms is entry-free.** -/
theorem conditionalMass_eq (α e : ℝ) (N : ℕ) (hα : 0 < α) (hN : 1 ≤ N)
    {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) (he : 0 < e) :
    stationaryMass α e N k / activeShare α e N = profile α k / profileSum α N := by
  rw [stationaryMass_eq α e N hα k hkN, activeShare_eq α e N hα hN]
  have hT : 0 < profileSum α N := profileSum_pos α N hα hN
  have hden : 0 < 1 + e * profileSum α N := by nlinarith
  have hk0 : k ≠ 0 := by omega
  simp [hk0]
  field_simp

end LeanMarx
