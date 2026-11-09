import LeanMarx.Selection

set_option linter.unusedSectionVars false

/-!
# Social metabolism: labour and price, with rent

Two numbers per commodity: its **labour value** `v c` and its **price** `p c`.
Labour value is the recursive embodiment

`v B = l + v A`,

i.e. the labour of a product equals its direct labour plus the labour embodied
in its inputs, integrated recursively (`isLabourValue_iff_recursion`, and
`producer_recursion_pointwise` for a single-output producer).

Prices are market prices.  They may diverge from labour values when a
commodity has a **single producer**: that producer can hold a rent wedge `μ`,
so that

`p c = (1 + μ c) · w · v c`   if `c` is monopolised,   `p c = w · v c` otherwise.

`μ > 0` is monopoly rent (price above value); `μ < 0` is monopsony rent (the
producer pays its suppliers below value, so its cost is below the value).
With several producers of `c` there is no wedge.

Aggregating, the price of the net product is the wage-weighted labour value
plus total rent:

`P = w · L + R`,

and the rent is exactly the sum over monopolised commodities.  If no commodity
is monopolised, `P = w · L`: the labour–price correspondence holds.
-/

namespace LeanMarx

open Classical Finset Matrix

variable {ι φ : Type*} [Fintype ι] [Fintype φ] [DecidableEq ι] [DecidableEq φ]

/-! ## Recursive labour value -/

/-- **Recursive embodiment.** `v` is a labour-value vector iff the labour
embodied in outputs equals direct labour plus the labour embodied in inputs. -/
theorem isLabourValue_iff_recursion (T : ProductionTable ι φ) (v : ι → ℝ) :
    T.IsLabourValue v ↔ v ᵥ* T.B = T.l + v ᵥ* T.A := by
  unfold ProductionTable.IsLabourValue ProductionTable.netOp
  rw [vecMul_sub, sub_eq_iff_eq_add]

/-- **Per-producer recursion.** For a single-output producer `p`, the labour
value of its commodity is its direct labour plus the labour embodied in its
inputs, summed recursively. -/
theorem producer_recursion_pointwise (T : ProducerTable ι φ) {v : ι → ℝ}
    (hv : T.toTable.IsLabourValue v) (p : φ) :
    v (T.output p) = T.labour p + ∑ i, v i * T.input i p := by
  have h := (isLabourValue_iff_recursion T.toTable v).mp hv
  have hp := congrFun h p
  have hB : (v ᵥ* T.toTable.B) p = v (T.output p) := by
    unfold ProducerTable.toTable
    simp only [vecMul, dotProduct]
    rw [Finset.sum_eq_single (T.output p)]
    · simp
    · intro i _ hi
      simp [hi]
    · intro h
      exact absurd (Finset.mem_univ (T.output p)) h
  have hA : (v ᵥ* T.toTable.A) p = ∑ i, v i * T.input i p := by
    unfold ProducerTable.toTable
    simp only [vecMul, dotProduct]
  rw [hB] at hp
  simp only [Pi.add_apply] at hp
  rw [hA] at hp
  simpa [ProducerTable.toTable] using hp

/-! ## Price, value and the rent wedge -/

/-- The price–labour gap per unit: `p c − w · v c`. -/
noncomputable def priceGap (p v : ι → ℝ) (w : ℝ) : ι → ℝ :=
  fun c => p c - w * v c

/-- The rent rate: the relative price–labour gap. -/
noncomputable def rentRate (p v : ι → ℝ) (w : ℝ) (c : ι) : ℝ :=
  p c / (w * v c) - 1

theorem price_eq_rentRate_mul {p v : ι → ℝ} {w : ℝ} {c : ι}
    (hw : w ≠ 0) (hv : v c ≠ 0) :
    p c = (1 + rentRate p v w c) * (w * v c) := by
  unfold rentRate
  field_simp
  ring

namespace ProducerTable

/-- A commodity has a single producer. -/
def IsMonopoly (T : ProducerTable ι φ) (c : ι) : Prop :=
  (T.producersOf c).card = 1

/-- With two or more producers there is no monopoly. -/
theorem not_isMonopoly_of_two {T : ProducerTable ι φ} {c : ι}
    (h : 2 ≤ (T.producersOf c).card) : ¬ T.IsMonopoly c := by
  unfold IsMonopoly
  omega

/-- The market price: a rent wedge is available only to a monopolist. -/
noncomputable def marketPrice (T : ProducerTable ι φ) (v : ι → ℝ) (w : ℝ)
    (μ : ι → ℝ) (c : ι) : ℝ :=
  (1 + if T.IsMonopoly c then μ c else 0) * (w * v c)

theorem marketPrice_of_monopoly (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {c : ι} (h : T.IsMonopoly c) :
    T.marketPrice v w μ c = (1 + μ c) * (w * v c) := by
  unfold marketPrice
  rw [if_pos h]

theorem marketPrice_of_not_monopoly (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {c : ι} (h : ¬ T.IsMonopoly c) :
    T.marketPrice v w μ c = w * v c := by
  unfold marketPrice
  rw [if_neg h]
  ring

/-- Rent on commodity `c` at net output `y`. -/
noncomputable def rent (T : ProducerTable ι φ) (v : ι → ℝ) (w : ℝ)
    (μ : ι → ℝ) (y : ι → ℝ) (c : ι) : ℝ :=
  (T.marketPrice v w μ c - w * v c) * y c

theorem rent_of_monopoly (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (h : T.IsMonopoly c) :
    T.rent v w μ y c = μ c * (w * v c) * y c := by
  unfold rent
  rw [marketPrice_of_monopoly T h]
  ring

theorem rent_of_not_monopoly (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (h : ¬ T.IsMonopoly c) :
    T.rent v w μ y c = 0 := by
  unfold rent
  rw [marketPrice_of_not_monopoly T h]
  ring

/-- A positive wedge under monopoly gives a positive rent. -/
theorem monopoly_rent_pos (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (hmono : T.IsMonopoly c)
    (hμ : 0 < μ c) (hw : 0 < w) (hv : 0 < v c) (hy : 0 < y c) :
    0 < T.rent v w μ y c := by
  rw [rent_of_monopoly T hmono]
  exact mul_pos (mul_pos hμ (mul_pos hw hv)) hy

/-- A negative wedge is monopsony rent: the price–value gap and the rent are
negative for the seller. -/
theorem monopsony_rent_neg (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (hmono : T.IsMonopoly c)
    (hμ : μ c < 0) (hw : 0 < w) (hv : 0 < v c) (hy : 0 < y c) :
    T.rent v w μ y c < 0 := by
  rw [rent_of_monopoly T hmono]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hμ (mul_pos hw hv)) hy

/-- **Rent scales with the wedge.** Under monopoly, rent is monotone in `μ`. -/
theorem rent_mono_markup (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ₁ μ₂ : ι → ℝ} {y : ι → ℝ} {c : ι} (hmono : T.IsMonopoly c)
    (hwv : 0 ≤ w * v c) (hy : 0 ≤ y c) (h : μ₁ c ≤ μ₂ c) :
    T.rent v w μ₁ y c ≤ T.rent v w μ₂ y c := by
  rw [rent_of_monopoly T hmono, rent_of_monopoly T hmono]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hwv) hy

/-- **Rent is positive exactly when the wedge is positive**, at a monopoly
with positive wage, labour value and output. -/
theorem rent_pos_iff (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (hmono : T.IsMonopoly c)
    (hw : 0 < w) (hv : 0 < v c) (hy : 0 < y c) :
    0 < T.rent v w μ y c ↔ 0 < μ c := by
  rw [rent_of_monopoly T hmono]
  constructor
  · intro h
    by_contra hμ
    have hμ' : μ c ≤ 0 := le_of_not_gt hμ
    have hneg : μ c * (w * v c) * y c ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hμ' (mul_pos hw hv).le) hy.le
    linarith
  · intro h
    exact mul_pos (mul_pos h (mul_pos hw hv)) hy

/-- No output, no rent. -/
theorem rent_eq_zero_of_output_zero (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (hy : y c = 0) :
    T.rent v w μ y c = 0 := by
  unfold rent
  rw [hy, mul_zero]

/-- No labour value, no rent. -/
theorem rent_eq_zero_of_value_zero (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (hv : v c = 0) :
    T.rent v w μ y c = 0 := by
  simp [rent, marketPrice, hv]

/-- No wage, no rent. -/
theorem rent_eq_zero_of_wage_zero (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ : ι → ℝ} {y : ι → ℝ} {c : ι} (hw : w = 0) :
    T.rent v w μ y c = 0 := by
  simp [rent, marketPrice, hw]

/-- **A second producer destroys the rent.** With two or more producers of a
commodity there is no wedge and no rent. -/
theorem rent_eq_zero_of_two_producers (T : ProducerTable ι φ) {v : ι → ℝ}
    {w : ℝ} {μ : ι → ℝ} {y : ι → ℝ} {c : ι}
    (h : 2 ≤ (T.producersOf c).card) : T.rent v w μ y c = 0 :=
  rent_of_not_monopoly T (not_isMonopoly_of_two h)

/-- Total rent. -/
noncomputable def aggregateRent (T : ProducerTable ι φ) (v : ι → ℝ) (w : ℝ)
    (μ : ι → ℝ) (y : ι → ℝ) : ℝ := ∑ c, T.rent v w μ y c

theorem aggregateRent_eq_gap_dot (T : ProducerTable ι φ) (v : ι → ℝ) (w : ℝ)
    (μ : ι → ℝ) (y : ι → ℝ) :
    T.aggregateRent v w μ y = priceGap (T.marketPrice v w μ) v w ⬝ᵥ y := by
  unfold aggregateRent rent priceGap dotProduct
  rfl

/-- **Aggregate rent rises with every wedge.** -/
theorem aggregateRent_mono_markup (T : ProducerTable ι φ) {v : ι → ℝ} {w : ℝ}
    {μ₁ μ₂ : ι → ℝ} {y : ι → ℝ} (hw : 0 ≤ w) (hv : ∀ c, 0 ≤ v c)
    (hy : ∀ c, 0 ≤ y c) (h : ∀ c, μ₁ c ≤ μ₂ c) :
    T.aggregateRent v w μ₁ y ≤ T.aggregateRent v w μ₂ y := by
  unfold aggregateRent
  refine Finset.sum_le_sum fun c _ => ?_
  by_cases hmono : T.IsMonopoly c
  · exact rent_mono_markup T hmono (mul_nonneg hw (hv c)) (hy c) (h c)
  · rw [rent_of_not_monopoly T hmono, rent_of_not_monopoly T hmono]

end ProducerTable

/-! ## The two aggregate numbers -/

/-- Labour embodied in the net product. -/
noncomputable def aggregateLabour (v y : ι → ℝ) : ℝ := v ⬝ᵥ y

/-- Price of the net product. -/
noncomputable def aggregatePrice (p y : ι → ℝ) : ℝ := p ⬝ᵥ y

/-- **Social metabolism in two numbers.** The price of net output is the
wage-weighted labour value plus total rent. -/
theorem aggregatePrice_eq_labour_add_rent (T : ProducerTable ι φ) (v : ι → ℝ)
    (w : ℝ) (μ : ι → ℝ) (y : ι → ℝ) :
    aggregatePrice (T.marketPrice v w μ) y
      = w * aggregateLabour v y + T.aggregateRent v w μ y := by
  rw [ProducerTable.aggregateRent_eq_gap_dot]
  unfold aggregatePrice aggregateLabour
  have hp : T.marketPrice v w μ = w • v + priceGap (T.marketPrice v w μ) v w := by
    ext c
    simp [priceGap]
  conv_lhs => rw [hp]
  rw [add_dotProduct, smul_dotProduct]
  ring

/-- **No monopoly, no defect.** If no commodity has a single producer, prices
are proportional to labour values at the wage rate. -/
theorem aggregatePrice_eq_of_no_monopoly (T : ProducerTable ι φ) (v : ι → ℝ)
    (w : ℝ) (μ : ι → ℝ) (y : ι → ℝ) (h : ∀ c, ¬ T.IsMonopoly c) :
    aggregatePrice (T.marketPrice v w μ) y = w * aggregateLabour v y := by
  rw [aggregatePrice_eq_labour_add_rent]
  have hrent : T.aggregateRent v w μ y = 0 := by
    unfold ProducerTable.aggregateRent
    exact Finset.sum_eq_zero fun c _ => ProducerTable.rent_of_not_monopoly T (h c)
  rw [hrent, add_zero]

/-- **Rent is the sum over monopolised commodities.** -/
theorem aggregateRent_eq_sum_monopolies (T : ProducerTable ι φ) (v : ι → ℝ)
    (w : ℝ) (μ : ι → ℝ) (y : ι → ℝ) :
    T.aggregateRent v w μ y
      = ∑ c ∈ Finset.univ.filter (fun c => T.IsMonopoly c),
          μ c * (w * v c) * y c := by
  classical
  unfold ProducerTable.aggregateRent
  have hsum : (∑ c, T.rent v w μ y c)
      = ∑ c, if T.IsMonopoly c then μ c * (w * v c) * y c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : T.IsMonopoly c
    · rw [ProducerTable.rent_of_monopoly T h]
      simp [h]
    · rw [ProducerTable.rent_of_not_monopoly T h]
      simp [h]
  rw [hsum, ← Finset.sum_filter]

/-! ## Supply, demand and price pressure -/

/-- Excess demand: demand minus supply at price `p`. -/
def ExcessDemand (D S : ι → ℝ → ℝ) (p : ι → ℝ) (c : ι) : ℝ :=
  D c (p c) - S c (p c)

/-- A market clears when excess demand is zero everywhere. -/
def MarketClears (D S : ι → ℝ → ℝ) (p : ι → ℝ) : Prop :=
  ∀ c, ExcessDemand D S p c = 0

/-- **Price pressure.** Positive excess demand raises the price. -/
theorem price_pressure {D S : ι → ℝ → ℝ} {p : ι → ℝ} {c : ι} {lam : ℝ}
    (hlam : 0 < lam) (h : 0 < ExcessDemand D S p c) :
    p c < p c + lam * ExcessDemand D S p c := by
  have := mul_pos hlam h
  linarith

/-- **Monopoly raises the price and lowers the quantity sold** when demand is
decreasing. -/
theorem monopoly_price_quantity {D : ι → ℝ → ℝ} {c : ι} (hD : Antitone (D c))
    {p₀ μ : ℝ} (hp₀ : 0 < p₀) (hμ : 0 < μ) :
    D c ((1 + μ) * p₀) ≤ D c p₀ :=
  hD (by nlinarith)

end LeanMarx
