import LeanMarx.Startups

set_option linter.unusedSectionVars false

/-!
# The cross-section of firm profit rates under entry and failure

A firm's rate `r` is observed only if it survives the rule `M' > M`, i.e. only
if `0 < r`.  So the observed cross-section is the underlying rate distribution
**truncated below at zero**, with a point mass at failure.  This module records
the finite-population consequences:

* the failure mass plus the survival mass is one;
* the survivor mean is at least the overall mean — selection raises the mean;
* the upper tail is unchanged by truncation: for `t > 0`, the set of firms
  above `t` is exactly the set of survivors above `t`, so the conditional tail
  probability is the unconditional tail count divided by the survival mass.
  Selection truncates the lower tail and renormalises; it does not create or
  destroy the upper tail.

The shape of the observed distribution is therefore: a mass at failure, a
right-skewed positive part, and an upper tail inherited from the rate process.
-/

namespace LeanMarx

open Finset

variable {φ : Type*} [Fintype φ] [DecidableEq φ]

/-- Firms with a positive rate, `0 < r p`. -/
noncomputable def survivors (r : φ → ℝ) : Finset φ :=
  univ.filter fun p => 0 < r p

/-- Firms with a nonpositive rate, `r p ≤ 0`: failure. -/
noncomputable def failures (r : φ → ℝ) : Finset φ :=
  univ.filter fun p => r p ≤ 0

theorem mem_survivors {r : φ → ℝ} {p : φ} : p ∈ survivors r ↔ 0 < r p := by
  simp [survivors]

theorem mem_failures {r : φ → ℝ} {p : φ} : p ∈ failures r ↔ r p ≤ 0 := by
  simp [failures]

theorem survivors_union_failures (r : φ → ℝ) : survivors r ∪ failures r = univ := by
  ext p
  simp only [mem_union, mem_univ, mem_survivors, mem_failures]
  exact ⟨fun _ => trivial, fun _ => by
    by_cases h : 0 < r p
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt h)⟩

theorem survivors_disjoint_failures (r : φ → ℝ) : Disjoint (survivors r) (failures r) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_survivors] at hp
  rw [mem_failures] at hq
  linarith

theorem card_survivors_add_card_failures (r : φ → ℝ) :
    (survivors r).card + (failures r).card = Fintype.card φ := by
  rw [← Finset.card_union_of_disjoint (survivors_disjoint_failures r),
    survivors_union_failures, Finset.card_univ]

/-- Fraction of firms that survive. -/
noncomputable def survivorMass (r : φ → ℝ) : ℝ :=
  (survivors r).card / Fintype.card φ

/-- Fraction of firms that fail. -/
noncomputable def failureMass (r : φ → ℝ) : ℝ :=
  (failures r).card / Fintype.card φ

theorem failureMass_add_survivorMass (r : φ → ℝ) (hN : Fintype.card φ ≠ 0) :
    failureMass r + survivorMass r = 1 := by
  unfold failureMass survivorMass
  rw [← add_div]
  have h : ((survivors r).card + (failures r).card : ℝ) = (Fintype.card φ : ℝ) := by
    exact_mod_cast card_survivors_add_card_failures r
  rw [add_comm, h, div_self]
  exact Nat.cast_ne_zero.mpr hN

/-- The mean rate over all firms. -/
noncomputable def overallMean (r : φ → ℝ) : ℝ :=
  (∑ p, r p) / Fintype.card φ

/-- The mean rate over survivors. -/
noncomputable def survivorMean (r : φ → ℝ) : ℝ :=
  (∑ p ∈ survivors r, r p) / (survivors r).card

theorem sum_eq_survivors_add_failures (r : φ → ℝ) :
    ∑ p, r p = (∑ p ∈ survivors r, r p) + ∑ p ∈ failures r, r p := by
  rw [← Finset.sum_union (survivors_disjoint_failures r), survivors_union_failures]

theorem failure_sum_nonpos (r : φ → ℝ) : ∑ p ∈ failures r, r p ≤ 0 := by
  apply Finset.sum_nonpos
  intro p hp
  exact mem_failures.mp hp

theorem survivor_sum_nonneg (r : φ → ℝ) : 0 ≤ ∑ p ∈ survivors r, r p := by
  apply Finset.sum_nonneg
  intro p hp
  exact le_of_lt (mem_survivors.mp hp)

/-- **Selection raises the mean.** The survivors' mean rate is at least the
overall mean, because the failed firms contribute only nonpositive rates. -/
theorem survivorMean_ge_overallMean (r : φ → ℝ) (hS : 0 < (survivors r).card)
    (hN : 0 < Fintype.card φ) : overallMean r ≤ survivorMean r := by
  unfold overallMean survivorMean
  have hsum : ∑ p, r p ≤ ∑ p ∈ survivors r, r p := by
    rw [sum_eq_survivors_add_failures]
    linarith [failure_sum_nonpos r]
  have hφ : 0 < (Fintype.card φ : ℝ) := by exact_mod_cast hN
  have hSc : 0 < ((survivors r).card : ℝ) := by exact_mod_cast hS
  have hle : ((survivors r).card : ℝ) ≤ (Fintype.card φ : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ _)
  have hSnonneg : 0 ≤ ∑ p ∈ survivors r, r p := survivor_sum_nonneg r
  calc
    (∑ p, r p) / (Fintype.card φ : ℝ)
        ≤ (∑ p ∈ survivors r, r p) / (Fintype.card φ : ℝ) :=
      div_le_div_of_nonneg_right hsum hφ.le
    _ ≤ (∑ p ∈ survivors r, r p) / ((survivors r).card : ℝ) :=
      div_le_div_of_nonneg_left hSnonneg hSc hle

/-- **Truncation preserves the upper tail.** For a positive threshold, the
survivors above it are exactly the firms above it. -/
theorem survivors_filter_eq (r : φ → ℝ) (t : ℝ) (ht : 0 < t) :
    (survivors r).filter (fun p => t < r p) = univ.filter (fun p => t < r p) := by
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_survivors]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨lt_trans ht h, h⟩

/-- The conditional upper-tail probability is the unconditional tail count
divided by the survival mass: selection rescales the tail, it does not change
it. -/
theorem survivor_tail_prob (r : φ → ℝ) (t : ℝ) (ht : 0 < t) :
    (((survivors r).filter (fun p => t < r p)).card : ℝ) / (survivors r).card
      = ((univ.filter (fun p => t < r p)).card : ℝ) / (survivors r).card := by
  rw [survivors_filter_eq r t ht]

end LeanMarx
