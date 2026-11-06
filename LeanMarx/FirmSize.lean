import LeanMarx.Death

set_option linter.unusedSectionVars false

/-!
# A finite growth/death/entry chain and its stationary firm-size distribution

State space `{0, 1, ..., N}`: `0` is the dead/entry pool; a firm of size `k`
(`1 ≤ k ≤ N`) either grows to `k+1` with probability `g k` or dies to `0` with
probability `1 - g k`.  The pool stays at `0` with probability `1 - e` and
enters at size `1` with probability `e`.  At the top, `g N = 0`.

With the size-dependent rule `g k = ((k+1)/(k+2))^α`, the stationary
distribution is explicit:

`π 0 = 1 / (1 + Σ_{k=1}^N e · ∏_{i=1}^{k-1} g i)`,   `π k = e (2/(k+1))^α / normaliser`.

The mass ratio is `π (k+1) / π k = ((k+1)/(k+2))^α → 1`, the signature of a
power-law tail.  A constant growth probability would instead give a constant
ratio `γ < 1` and geometric decay.  So size-dependent growth and death —
growth probability rising with size — is what turns the stationary
distribution from geometric into Pareto-like.

This is a finite-state chain: the tail is truncated at `N`, and the invariant
distribution is verified by the global balance equations, not by a
Markov-chain existence theorem.
-/

namespace LeanMarx

open Filter Finset
open scoped Topology

/-- The telescoping identity
`Σ_{j<N} (∏_{i<j} g (i+1)) (1 - g (j+1)) = 1 - ∏_{i<N} g (i+1)`. -/
theorem telescope (g : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, (∏ i ∈ Finset.range j, g (i + 1)) * (1 - g (j + 1))
      = 1 - ∏ i ∈ Finset.range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
      ring

/-- Growth probability from size `k` to `k+1`, truncated at the top state. -/
noncomputable def growthAt (α : ℝ) (N k : ℕ) : ℝ :=
  if k < N then ((k + 1 : ℝ) / (k + 2 : ℝ)) ^ α else 0

/-- Unnormalised stationary mass of size `k`. -/
noncomputable def mass (α e : ℝ) (N k : ℕ) : ℝ :=
  e * ∏ i ∈ Finset.range (k - 1), growthAt α N (i + 1)

/-- Normalising constant. -/
noncomputable def norm (α e : ℝ) (N : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range N, mass α e N (k + 1)

/-- Stationary distribution of the finite chain. -/
noncomputable def stationaryMass (α e : ℝ) (N k : ℕ) : ℝ :=
  if k = 0 then 1 / norm α e N else mass α e N k / norm α e N

/-! ## The power-law masses -/

theorem prod_growthAt_aux (α : ℝ) {n N : ℕ} (h : n < N) :
    ∏ i ∈ Finset.range n, growthAt α N (i + 1) = (2 / ((n : ℝ) + 2)) ^ α := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : n < N := by omega
      rw [Finset.prod_range_succ, ih hn]
      have hg : growthAt α N (n + 1) = (((n : ℝ) + 2) / ((n : ℝ) + 3)) ^ α := by
        rw [show growthAt α N (n + 1)
              = ((↑(n + 1) + 1) / (↑(n + 1) + 2)) ^ α by
          simp [growthAt, show n + 1 < N by omega]]
        congr 1
        push_cast
        ring
      rw [hg]
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      have hbase : (2 / ((n : ℝ) + 2)) * (((n : ℝ) + 2) / ((n : ℝ) + 3))
          = 2 / ((n : ℝ) + 3) := by
        field_simp
      rw [hbase]
      have hidx : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by
        push_cast
        ring
      rw [hidx]

theorem mass_eq (α e : ℝ) (N : ℕ) (_hα : 0 < α) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    mass α e N k = e * (2 / ((k : ℝ) + 1)) ^ α := by
  unfold mass
  have hkN' : k - 1 < N := by
    have hkpos : 0 < k := by omega
    exact lt_of_lt_of_le (Nat.sub_one_lt (by omega : k ≠ 0)) hkN
  rw [prod_growthAt_aux α (n := k - 1) (N := N) hkN']
  have hidx : (((k - 1 : ℕ) : ℝ) + 2) = (k : ℝ) + 1 := by
    rw [Nat.cast_sub hk]
    ring
  rw [hidx]

theorem mass_pos (α e : ℝ) (N : ℕ) (hα : 0 < α) (he : 0 < e) {k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) : 0 < mass α e N k := by
  rw [mass_eq α e N hα hk hkN]
  exact mul_pos he (Real.rpow_pos_of_pos (by positivity) α)

theorem norm_pos (α e : ℝ) (N : ℕ) (_hN : 1 ≤ N) (hα : 0 < α) (he : 0 < e) :
    0 < norm α e N := by
  unfold norm
  have h : 0 ≤ ∑ k ∈ Finset.range N, mass α e N (k + 1) := by
    apply Finset.sum_nonneg
    intro k hk
    have hkN : k + 1 ≤ N := by
      have := Finset.mem_range.mp hk
      omega
    exact (mass_pos α e N hα he (by omega) hkN).le
  linarith

theorem prod_growthAt_zero (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∏ i ∈ Finset.range N, growthAt α N (i + 1) = 0 := by
  refine Finset.prod_eq_zero (i := N - 1) ?_ ?_
  · rw [Finset.mem_range]
    omega
  · rw [show N - 1 + 1 = N by omega]
    simp [growthAt]

/-! ## Normalisation -/

theorem sum_stationaryMass (α e : ℝ) (N : ℕ) (hN : 1 ≤ N) (hα : 0 < α) (he : 0 < e) :
    ∑ k ∈ Finset.range (N + 1), stationaryMass α e N k = 1 := by
  rw [Finset.sum_range_succ']
  have h0 : stationaryMass α e N 0 = 1 / norm α e N := by simp [stationaryMass]
  have hk : ∀ k, stationaryMass α e N (k + 1) = mass α e N (k + 1) / norm α e N := by
    intro k
    simp [stationaryMass]
  rw [h0]
  simp_rw [hk]
  rw [← Finset.sum_div]
  have hn : norm α e N = 1 + ∑ k ∈ Finset.range N, mass α e N (k + 1) := rfl
  rw [hn]
  have hne : (1 + ∑ k ∈ Finset.range N, mass α e N (k + 1)) ≠ 0 := by
    rw [← hn]
    exact (norm_pos α e N hN hα he).ne'
  field_simp
  ring

/-- The stationary masses are positive, so they form a probability vector. -/
theorem stationaryMass_pos (α e : ℝ) (N k : ℕ) (hN : 1 ≤ N) (hα : 0 < α)
    (he : 0 < e) (hk : k ≤ N) : 0 < stationaryMass α e N k := by
  have hnorm := norm_pos α e N hN hα he
  by_cases hk0 : k = 0
  · subst hk0
    simpa [stationaryMass] using hnorm
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    simp [stationaryMass, hk0]
    exact div_pos (mass_pos α e N hα he hk1 hk) hnorm

/-! ## Balance equations -/

/-- The inflow to the dead/entry pool equals its outflow. -/
theorem stationary_balance_zero (α e : ℝ) (N : ℕ) (hN : 1 ≤ N) (hα : 0 < α)
    (he : 0 < e) :
    stationaryMass α e N 0
      = stationaryMass α e N 0 * (1 - e)
        + ∑ k ∈ Finset.range N,
            stationaryMass α e N (k + 1) * (1 - growthAt α N (k + 1)) := by
  have hsum : ∑ k ∈ Finset.range N,
      mass α e N (k + 1) * (1 - growthAt α N (k + 1)) = e := by
    have hmass : ∀ k, mass α e N (k + 1)
        = e * ∏ i ∈ Finset.range k, growthAt α N (i + 1) := by
      intro k
      unfold mass
      rw [show k + 1 - 1 = k by omega]
    calc ∑ k ∈ Finset.range N,
          mass α e N (k + 1) * (1 - growthAt α N (k + 1))
        = ∑ k ∈ Finset.range N,
            e * ((∏ i ∈ Finset.range k, growthAt α N (i + 1))
              * (1 - growthAt α N (k + 1))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hmass k]
          ring
      _ = e * ∑ k ∈ Finset.range N,
            (∏ i ∈ Finset.range k, growthAt α N (i + 1))
              * (1 - growthAt α N (k + 1)) := by
          rw [Finset.mul_sum]
      _ = e * (1 - ∏ i ∈ Finset.range N, growthAt α N (i + 1)) := by
          rw [telescope]
      _ = e := by
          rw [prod_growthAt_zero α hN]
          ring
  have h0 : stationaryMass α e N 0 = 1 / norm α e N := by simp [stationaryMass]
  have hk : ∀ k, stationaryMass α e N (k + 1) = mass α e N (k + 1) / norm α e N := by
    intro k
    simp [stationaryMass]
  rw [h0]
  simp_rw [hk]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hsum]
  have hne : norm α e N ≠ 0 := (norm_pos α e N hN hα he).ne'
  field_simp
  ring

/-- The inflow to each size `k+1` equals its outflow. -/
theorem stationary_balance_succ (α e : ℝ) (N : ℕ) (hN : 1 ≤ N) (hα : 0 < α)
    (he : 0 < e) :
    ∀ k ∈ Finset.range N,
      stationaryMass α e N (k + 1)
        = if k = 0 then stationaryMass α e N 0 * e
          else stationaryMass α e N k * growthAt α N k := by
  intro k _
  have hne : norm α e N ≠ 0 := (norm_pos α e N hN hα he).ne'
  by_cases hk0 : k = 0
  · subst hk0
    simp [stationaryMass, mass]
    field_simp
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hprod : (∏ i ∈ Finset.range k, growthAt α N (i + 1))
        = (∏ i ∈ Finset.range (k - 1), growthAt α N (i + 1)) * growthAt α N k := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [Finset.prod_range_succ]
      rw [show k - 1 + 1 = k by omega]
    have hm : mass α e N (k + 1) = mass α e N k * growthAt α N k := by
      unfold mass
      rw [show k + 1 - 1 = k by omega]
      rw [hprod]
      ring
    simp only [stationaryMass, ite_eq_right (by omega : k + 1 ≠ 0), ite_eq_right hk0, hm]
    field_simp

/-! ## The tail -/

/-- The stationary mass ratio for the size-dependent rule. -/
theorem mass_ratio (α e : ℝ) (N : ℕ) (hα : 0 < α) (he : 0 < e) {k : ℕ}
    (hk : 1 ≤ k) (hkN : k + 1 ≤ N) :
    mass α e N (k + 1) / mass α e N k
      = (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ α := by
  rw [mass_eq α e N hα (by omega) hkN, mass_eq α e N hα hk (by omega)]
  rw [mul_div_mul_left _ _ he.ne']
  rw [← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp
  push_cast
  ring

/-- The mass ratio tends to one: the stationary masses form a power law, not a
geometric distribution. -/
theorem ratio_tendsto_one (α : ℝ) :
    Tendsto (fun k : ℕ => (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ α) atTop (𝓝 1) := by
  have hbase : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2)) atTop (𝓝 1) := by
    have hg : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hsmall : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      simpa using hg.const_div_atTop (1 : ℝ)
    have hsub : Tendsto (fun k : ℕ => 1 - (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hsmall)
    convert hsub using 1
    ext k
    field_simp
    ring
  have hcont : ContinuousAt (fun x : ℝ => x ^ α) 1 :=
    Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)
  have hcomp := hcont.tendsto.comp hbase
  have hfun : ((fun x : ℝ => x ^ α) ∘ fun k : ℕ => ((k : ℝ) + 1) / ((k : ℝ) + 2))
      = fun k : ℕ => (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ α := by
    funext k
    rfl
  rw [hfun] at hcomp
  simpa [Real.one_rpow] using hcomp

end LeanMarx
