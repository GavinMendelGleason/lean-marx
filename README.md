# lean-marx

A formal development in Lean 4 of two questions about an input–output
production table:

1. **When does the table determine labour values, and how do cost prices
   relate to them?** `LeanMarx/Basic.lean`, `LeanMarx/Price.lean`
2. **How is income distributed between workers and capitalists when everyone
   may be a mixture of the two?** `LeanMarx/Distribution.lean`

Surplus value is derived from the table in `LeanMarx/Surplus.lean`.

The primitive object is the **production table**, not a price system: there is
no Sraffa equation and no assumed uniform profit rate.

## Building

The toolchain comes from Nix; Mathlib is pinned by revision in
`lakefile.toml`.

```bash
nix develop -c lake exe cache get   # prebuilt Mathlib oleans
nix develop -c lake build
```

`nix develop` supplies `elan` and the build tools from nixpkgs, pinned by
`flake.lock`; `lean-toolchain` selects the official Lean 4.35.0 release, which
elan provisions. The official release matters: oleans are tied to the compiler
build, and nixpkgs' own Lean build cannot load the Mathlib cache. The first
`lake exe cache get` fetches Mathlib at the revision in `lakefile.toml` and
unpacks its cache; without it the first build compiles Mathlib from source.

An audit of the axioms used by the main results:

```bash
nix develop -c lake env lean LeanMarxAudit.lean
```

## The production table

Commodities `ι`, activities `j`, both finite:

- `A i k` — commodity `i` used per unit of activity `k` (the use matrix);
- `B i k` — commodity `i` produced per unit of activity `k` (the make matrix;
  several rows of a column may be nonzero, so joint production is allowed);
- `l k` — labour input per unit of activity `k`, a row of the input side.

The table fixes the **net-output operator** `N = B − A`. Activity `x` yields
net output `N *ᵥ x` and employment `l ⬝ᵥ x`. The single-product model is the
case `B = 1`.

## Feature 1 — labour values and cost prices

**Labour values** are the vectors `v` with

```
v (B − A) = l.
```

With joint production `N` is rectangular and need not be invertible, so this
is a real condition, not a definition:

| Predicate | Meaning | Consequence |
|---|---|---|
| `ValuesExist` | `N` has a left inverse (injective) | every labour input vector has a labour value |
| `ValuesUnique` | `N` has a right inverse (surjective) | a labour value is unique when it exists |
| `DeterminesValues` | both | `∃! v, IsLabourValue v` |

Both together are invertibility of `N`. `LeanMarxDemo.lean` shows all three
outcomes: the single-product table (`B = 1`) determines values; a genuine
joint-production table with `N = [[1,1],[0,1]]` still does; and a table whose
two processes have the same net output `(1,1)` does not — it admits two
distinct value vectors for `l = (1,1)`, and none at all for `l = (1,0)`.

**Cost prices** are the dual of the table, with no markup theory:

```
p (B − A) = w l.
```

The consequences are theorems:

| Result | Statement |
|---|---|
| `costPrice_exists_iff` | a cost price exists exactly when a labour value does (same linear system, scaled by `w`) |
| `costPrice_eq_smul_labourValue` | when values are unique, every cost price is `w • v` |
| `costPrice_netOutput` | the value of net output at cost prices is exactly the wage bill |
| `costPrice_wage_value_of_labour_power` | with the wage equal to the price of the real wage bundle, `v·b = 1`: cost prices leave no surplus |

So the price–value correspondence is not a special condition to be searched
for; it is automatic whenever the table determines labour values. The burden
falls on the **rank condition**, which joint production can break — and no
pricing convention can repair a table that does not determine values.

Because cost pricing exhausts net output in wages, profit is not a price
residual. It is carried by the distributional parameters of feature 2, and
surplus value is defined separately from the table.

## Feature 2 — income distribution with mixed agents

`LeanMarx/Distribution` models a population in which agent `i` owns labour
`ℓ i` and capital `k i`. At wage rate `w` and profit rate `π`:

```
y i = w · ℓ i + π · k i,        s i = y i / Σ y.
```

Every income share is a convex combination of the agent's labour share and
capital share, with the economy-wide wage and profit shares as weights:

```
s i = ω · (ℓ i / L) + (1 − ω) · (k i / K).
```

Formalised consequences:

| Result | Statement |
|---|---|
| Mixture | the identity above, under `L ≠ 0`, `K ≠ 0`, `Σy ≠ 0`; |
| Weights | `ω + (1 − ω) = 1`, and both are nonnegative for nonnegative wages, profit rate and endowments; |
| **Equal mixtures** | if `k i = ρ · ℓ i` for all `i`, then `s i = ℓ i / L` — the class split has no effect on relative incomes; |
| Pure worker | `k i = 0` gives `s i = ω · (ℓ i / L)`; |
| **Inequality bound** | `Gini(y) ≤ ω · Gini(ℓ) + (1 − ω) · Gini(k)`: mixing distributions can only offset differences. |

`Distribution.lean` is independent of the price model: `w` and `π` are
parameters, and the table enters only through employment and capital if one
chooses to identify them (see the limits section).

## Time

`LeanMarx/Circuit.lean` has the one-turn circuit; `LeanMarx/Dynamics.lean`
iterates it and adds a balanced-growth path for the table.

**Balanced growth.** A `BalancedPath` satisfies `x (t+1) = (1+g) x t`, hence
`x t = (1+g)^t x 0`. Employment, net output and the money value of net output
all grow at `1+g`:

| Result | Statement |
|---|---|
| `BalancedPath.x_eq` | `x t = (1+g)^t • x 0` |
| `employment_eq` | `employment (x t) = (1+g)^t * employment x 0` |
| `netOutput_eq` | `netOutput (x t) = (1+g)^t • netOutput x 0` |
| `price_netOutput_eq` | `p ⬝ᵥ netOutput (x t) = (1+g)^t * p ⬝ᵥ netOutput x 0` |

Labour values and cost prices are stationary, so value accounting holds at
every date.

**Capital circuit.** With a per-investor profit rate,
`w (t+1) i = (1+π i) w t i`, solved uniquely by `w t i = (1+π i)^t w0 i`:

| Result | Statement |
|---|---|
| `circuit_unique` | the circuit law with a given initial wealth has one solution |
| `share_wealthAt_uniform` | equal rates preserve every share at every date |
| `gini_wealthAt_uniform` | equal rates preserve the Gini coefficient |
| `sum_wealthAt_uniform` | total capital grows at `1+π` |
| `tendsto_share_dominant` | if one rate strictly dominates, its share tends to 1 |

So the circuit with equal rates is share-preserving at every date; with
differential rates it concentrates wealth into a point mass, which is also not
a power law. A non-degenerate Pareto distribution therefore needs what the
circuit does not contain — stochastic shocks with a reflecting barrier or
reset, or a rich-get-richer mechanism. Independent multiplicative shocks alone
(Gibrat) point towards a lognormal cross-section.

## Investment and preferential attachment

`LeanMarx/Investment.lean` lets agents invest capital and distributes the
period's surplus. Total investment is `K = Σ I i`; the surplus is `π K` and an
allocation `s` with `Σ s = 1` moves each agent's capital

```
M i  →  M i + ΔM i,      ΔM i = π K · s i.
```

The rate `π` can be the table's value rate of profit
(`ProductionTable.valueProfitRate`).

| Result | Statement |
|---|---|
| `investStep_attach` | proportional allocation (`s i = M i / W`) scales every agent by `1 + πK/W` |
| `investStep_attach_share` | hence shares are unchanged |
| `attachProb_strictMono` | richer agents are strictly more likely to receive the next unit |
| `expected_share_attachment` | random proportional attachment preserves the expected share exactly |
| `preferential_increases_share` | if `s j > M j / W` and `Δ > 0`, the share of `j` rises |
| `winner_share_increases` | winner-takes-all raises the winner's share |
| **`tendsto_winnerPath_share`** | with a positive surplus, the winner's share tends to `1` |

So preferential allocation is a real rich-get-richer mechanism: proportional
attachment is scale-invariant (and preserves expected shares), while any
strictly preferential rule raises the favoured share, and winner-takes-all
concentrates into a point mass. A **power law over agents** is still not
produced: with a fixed finite set, proportional attachment is a Pólya urn
(Dirichlet limit), and preferential rules degenerate. The Yule/Simon power law
needs entry — new agents taking a share of the surplus — which is not
formalised here.

## Investment by expected profit rates

`LeanMarx/Expectations.lean` assumes investors allocate capital across
activities in proportion to their **expected profit rates** `r : σ → ℝ`:

```
rateShare r a = r a / Σ b, r b,
investIn M r i a = M i * rateShare r a,
totalInvested M r a = (Σ i, M i) * rateShare r a.
```

| Result | Statement |
|---|---|
| `sum_rateShare` | the rate shares form a probability distribution |
| `rateShare_strictMono` | a higher expected rate receives a larger share |
| `totalInvested_eq` | aggregate investment in an activity is independent of the wealth distribution |
| `expectedReturnRate_eq` | the expected return is `ρ̄ = (Σ r²) / (Σ r)` |
| `expectedWealth_share` | common expectations leave every wealth share unchanged |
| `expectedWealth_gini` | common expectations leave the Gini coefficient unchanged |
| `share_increases_iff_above_average` | an investor gains share exactly when their expected return exceeds the average |
| `expectedWealthOf_iterate` | iterating fixed expected returns is the circuit path `wealthAt ρ M0` |
| `tendsto_share_expected_dominant` | a strictly dominant expected return drives its share to `1` |

So investing by expected profit rates is not by itself a distributional
mechanism: with common expectations every investor earns the same
rate-weighted average, so shares and inequality are frozen. What moves the
distribution is **heterogeneous** expectations — an investor whose expected
return is above the economy-wide average gains share, one below it loses.
With fixed expectations the iteration is the circuit of `Dynamics`, so the
outcome is either a frozen distribution (equal rates) or a point mass
(`tendsto_share_expected_dominant`). A Pareto law would require a specific
persistent distribution of expected returns across investors, or a stochastic
barrier/entry mechanism; neither is derived here.

## Producers and bankruptcy

`LeanMarx/Selection.lean` makes the producers explicit. A `ProducerTable` has
a column per producer, each making one indexed commodity (`output : φ → ι`);
several producers may make the same commodity, so an industry can have more
than one technique. It embeds into the general table via `toTable`, whose net
output for producer `p` is one unit of its commodity less its inputs
(`toTable_netOp_apply`).

A producer's capital reproduces as `M' = M (1 + r)` and it **survives only if
`M' > M`**; if `M' ≤ M` it goes bankrupt:

| Result | Statement |
|---|---|
| `survives_iff` | `M < M'` exactly when `r > 0` |
| `bankrupt_iff` | `M' ≤ M` exactly when `r ≤ 0` |
| `tendsto_capitalPath_zero` | with `-1 < r < 0`, capital decays geometrically to zero |
| `exitStep_of_bankrupt` | a nonpositive-rate producer exits at zero capital |
| `exitStep_of_survivor` | a positive-rate producer grows |
| `exitStep_pos_rate` | after exit, any producer with capital has a positive rate |
| `tendsto_share_selected` | a strictly dominant producer takes the whole capital share |

Exit is the ingredient the earlier models lacked. Multiplicative growth plus
bankruptcy is the classical setup for a Pareto firm-size distribution, but the
power law needs **entry** of new producers and stochastic growth on top of
exit; deterministic selection and growth still drive the distribution to a
point mass.

## Startups

`LeanMarx/Startups.lean` lets investors found new producers. An investor
commits `c = θ M` of wealth to a startup with expected rate `r`; survival is
again `M' > M`:

| Result | Statement |
|---|---|
| `Startup.survives_iff` | a startup survives exactly when `0 < r` |
| `Startup.gain_of_survives` | success changes value by `+ c r` |
| `Startup.loss_of_bankrupt` | failure loses the committed capital `c` |
| `wealthAfterStartup_of_survives` | `M' = M + c r` |
| `wealthAfterStartup_of_bankrupt` | `M' = M - c` |
| `expectedStartupWealth_eq` | expected wealth is `M + c (p r - (1 - p))` |
| `expectedStartupWealth_gain_iff` | positive expected gain exactly when `1 < p (1 + r)` |
| `entry_startup_bankrupt` | a nonpositive-rate startup exits on entry |
| `entry_startup_survives` | a positive-rate startup enters and grows |
| `sum_entryCapital` | capital after entry is old capital plus startup capital |

Entry, exit and growth are now all present. A stationary power law still
requires a stochastic distribution of startup outcomes: the deterministic
model either freezes shares or concentrates them.

## Stochastic death around the average

`LeanMarx/Death.lean` makes death a probability. A producer's rate `r` is
compared with the capital-weighted average `r̄`, and the death probability is
the lower tail of a Gaussian centred at `r̄`:

```
deathProb r r̄ σ = Φ ((r̄ - r) / σ),
```

where `Φ` is the standard normal CDF (`normalCdf`, built from Mathlib's
`gaussianPDFReal`).

| Result | Statement |
|---|---|
| `normalCdf_zero` | `Φ 0 = 1/2` |
| `deathProb_nonneg`, `deathProb_le_one` | death is a probability |
| `deathProb_antitone` | lower rates die more often |
| `deathProb_avg` | at the average, death is `1/2` |
| `deathProb_below_avg` | below average, death is at least `1/2` |
| `deathProb_above_avg` | above average, death is at most `1/2` |
| `sum_deviation_eq_zero` | capital-weighted deviations from the average sum to zero |
| `expectedGrowth_le_of_le` | expected growth is increasing in the rate |

So the lower tail is pruned in proportion to how far a producer falls below
the average, while the deviations balance exactly. This is the stochastic
ingredient the deterministic selection models lacked. A stationary power law
still needs the full stochastic process — entry, the law of motion at every
date, and a stationary distribution — which is not derived here.

## Stationary firm sizes and the wealth distribution

`LeanMarx/FirmSize.lean` builds the finite chain the previous sections were
missing. States are `{0, …, N}`: `0` is the dead/entry pool; a firm of size
`k` grows to `k+1` with probability `g k` or dies to `0` with `1 - g k`; the
pool enters at size `1` with probability `e`. At the top, `g N = 0`.

With the size-dependent rule

```
g k = ((k+1)/(k+2))^α,
```

the stationary distribution is explicit:

```
π 0 = 1 / (1 + Σ_{k=1}^N e (2/(k+1))^α),
π k  = e (2/(k+1))^α / (1 + Σ_{k=1}^N e (2/(k+1))^α).
```

| Result | Statement |
|---|---|
| `telescope` | the entry/death balance telescopes |
| `mass_eq` | the stationary mass is `e (2/(k+1))^α` |
| `stationaryMass_pos` | the masses form a probability vector |
| `sum_stationaryMass` | they sum to one |
| `stationary_balance_zero` | inflow to the pool equals outflow |
| `stationary_balance_succ` | inflow to each size equals outflow |
| `mass_ratio` | `π(k+1)/πk = ((k+1)/(k+2))^α` |
| `ratio_tendsto_one` | that ratio tends to `1` |
| `mass_ratio_eq_one_sub_deathHazard` | `π(k+1)/πk = 1 − h k`, the death hazard |
| `deathHazard_antitone` | the death hazard falls with size |
| `deathHazard_tendsto_zero` | the death hazard vanishes in the tail |

The mass ratio is one minus the death hazard. So a power-law tail — the mass
ratio tending to one — is exactly a death hazard that vanishes with size. A
constant growth probability, and therefore a constant hazard, gives a constant
ratio and a geometric tail. This is the formal counterpart of the observation
that a lognormal body plus a Pareto tail suggests different hazard regimes:
the tail needs a size-declining hazard, while the body is compatible with a
constant hazard. The cross-section alone does not identify the hazard, though;
transition data are needed.

So the stationary firm-size distribution — and with one firm per investor, the
stationary wealth distribution — is a **truncated power law**: `π k ∝
(k+1)^{-α}`. The mass ratio tending to one is the signature of a power-law
tail; a constant growth probability would instead give a constant ratio
`γ < 1` and geometric decay. The exponent is controlled by how strongly the
growth probability rises with size: larger `α` means a heavier tail.

## The wealth pump and entry

`LeanMarx/WealthPump.lean` factors the stationary masses:

```
π k = e A k / (1 + e Σ A),     π 0 = 1 / (1 + e Σ A),     A k = (2/(k+1))^α.
```

| Result | Statement |
|---|---|
| `stationaryMass_eq` | the factored form |
| `deadMass_eq` | `π₀ = 1/(1+eΣA)` |
| `activeShare_add_deadMass` | active share `+` dead mass `= 1` |
| `zeroMass_strictAnti` | lower entry raises the zero-wealth mass |
| `activeShare_strictMono` | higher entry raises the active sector |
| `throughput_strictMono` | higher entry raises the gross inflow up the ladder |
| `conditionalMass_eq` | the distribution among active firms is entry-free |
| `mass_ratio` (FirmSize) | the tail ratio is entry-free |

Here `π₀` is the **dead / zero-wealth mass**: the stationary share of the
population in state `0`, which is a single reservoir standing for both a
bankrupt producer and an agent that has not entered. State `0` carries zero
capital, so `π₀` is also the share of agents with zero wealth. The active
share is exactly `1 − π₀` (`activeShare_add_deadMass`).

Entry is the extensive margin. It changes how many agents are active and how
much flow passes up the ladder; it does not change the shape of the
distribution among active firms, the top share among owners, or the Pareto
exponent. Measured inequality across the whole population rises when entry
falls, because the zero-wealth mass grows. The intensity of the pump itself is
set by the size dependence of growth and death, not by entry.

## Banking, debt and comparative models

`LeanMarx/Banking.lean` adds the accounting core of a monetary production
economy.

| Result | Statement |
|---|---|
| `assets_eq_liabilities_add_equity` | the balance-sheet identity |
| `equity_createLoan` | a loan of `L` creates a deposit of `L`; equity is unchanged |
| `equity_repayLoan` | repayment destroys both sides; equity is unchanged |
| `equity_writeOff` | a write-off reduces equity by the loss |
| `Firm.insolvent_iff` | insolvency is debt exceeding assets |
| `investment_of_no_credit` | zero credit recovers retained-earnings investment |
| `investment_le_retained_add_capacity` | investment is capped by retained earnings plus the credit limit |
| `creditCapacity_mono_leverage` | higher leverage raises lending capacity |

Money is endogenous: deposits are created by lending and destroyed by
repayment.  The credit limit and the leverage ratio are the comparative
parameters for the financial sector.

`LeanMarx/Comparative.lean` formalises the model stack.  The real model is
`K' = K(1+π)`; the financed model adds credit, `K' = K(1+π) + c`.

| Result | Statement |
|---|---|
| `step_projection_of_no_credit` | with `c = 0`, the financed step projects onto the real step |
| `credit_stepN` | zero credit is preserved along the trajectory |
| `iterate_projection` | the whole financed trajectory projects onto the real one |
| `credit_increases_capital` | nonnegative credit does not lower capital |
| `capital_mono_credit` | higher credit gives higher capital |

So each layer is a **conservative extension** with a switch-off reduction to
the layer below.  The intended stack is

```
production → investment → debt → banking → central banking
```

with two kinds of comparison at each step: *vertical* (the reduction theorem
when the new feature is switched off) and *horizontal* (comparative statics
within the layer: credit limit, leverage, interest rate, default).

Not yet modelled: reserves and the central bank, deposit insurance,
households' portfolio choice, default as a discontinuity, and the open
economy.  The next layer should add a lending rule with capital adequacy and
collateral, then a default event with losses and bank failure.

## Labour values versus commodity substitution

Under cost pricing and unique labour values, prices are exactly proportional
to labour values:

```
p = w • v,      p i / p j = v i / v j.
```

| Result | Statement |
|---|---|
| `price_ratio_eq_value_ratio` | the price ratio is the labour-value ratio |
| `price_eq_value_of_unit_wage` | with `w = 1`, price equals labour value |
| `price_eq_labour_add_gap` | `p = w • v + gap` |
| `priceGap_eq_zero_iff` | zero gap iff prices are proportional to values |
| `marketPrice_gap_eq` | at model prices the gap is the rent wedge |
| `marketPrice_gap_zero_of_no_monopoly` | no monopoly ⇒ gap zero |

This is the strongest statement the model supports: the labour-value vector is
a sufficient statistic for relative prices.  A **commodity substitution** acts
on the input matrix, so it changes `v` and `p` together; the correspondence is
preserved for the new table.  Substitution is therefore the *basis* of the
labour values, not an alternative determinant of price.

What breaks the determination is distribution and market structure.  The
decomposition is

```
p = w • v + gap,        gap = p − w • v.
```

At the model's prices the gap is exactly the rent wedge.  A monopoly, a
markup, a rent, joint production or a non-unique value vector makes the gap
nonzero or the value vector unavailable.  Demand substitution is a separate
channel: in the cost-price model demand determines quantities, not prices;
with markups, demand elasticity feeds into the markup and hence into the gap,
not into the labour values.

The cost-price result is a zero-profit benchmark.  With a uniform profit rate,
prices are not proportional to labour values in general — that is the
transformation problem, and `LeanMarx/Correspondence` and
`LeanMarx/RentTheory` locate where the correspondence holds and where the
deviation enters.

## Social metabolism: labour, price and rent

`LeanMarx/SocialMetabolism.lean` keeps the two numbers per commodity: labour
value `v c` and price `p c`.

Labour value is recursive (`isLabourValue_iff_recursion`):

```
v B = l + v A.
```

For a single-output producer this reads
`v (output p) = labour p + Σ i, v i * input i p`
(`producer_recursion_pointwise`): direct labour plus the labour embodied in
inputs, integrated recursively.

Prices are market prices. A rent wedge exists only where a commodity has a
single producer (`IsMonopoly c`, i.e. `producersOf c` has one element):

```
p c = (1 + μ c) * w * v c   if monopolised,
p c = w * v c               otherwise.
```

`μ > 0` is monopoly rent (price above value); `μ < 0` is monopsony rent
(suppliers paid below value). With two or more producers there is no wedge
(`not_isMonopoly_of_two`).

| Result | Statement |
|---|---|
| `marketPrice_of_monopoly` | monopoly price includes the wedge |
| `marketPrice_of_not_monopoly` | competitive price equals the labour value |
| `rent_of_monopoly` | rent `= μ c * (w * v c) * y c` |
| `rent_of_not_monopoly` | rent is zero |
| `monopoly_rent_pos`, `monopsony_rent_neg` | signs of the rent |
| `aggregatePrice_eq_labour_add_rent` | `P = w L + R` |
| `aggregatePrice_eq_of_no_monopoly` | no monopoly ⇒ `P = w L` |
| `aggregateRent_eq_sum_monopolies` | `R` is the sum over monopolised commodities |
| `price_pressure` | positive excess demand raises the price |
| `monopoly_price_quantity` | a monopoly markup lowers the quantity sold |

So the two-number summary is `(L, P)` with `P = w L + R`. The defect between
labour and price is exactly the rent term, and it is non-zero only where
market power exists — a single producer of an indexed commodity.

**What produces rent.** The incidence is

```
rent c = μ c · w · v c · y c,
```

so rent is larger when the wedge `μ` is larger, the wage is higher, the
commodity is more labour-intensive, and its output is larger. The necessary
conditions are tight:

| Result | Statement |
|---|---|
| `rent_of_not_monopoly` | no single producer, no wedge, no rent |
| `rent_eq_zero_of_two_producers` | a second producer destroys the monopoly and the rent |
| `rent_pos_iff` | under monopoly, with `w, v c, y c > 0`, rent `> 0` iff `μ c > 0` |
| `rent_eq_zero_of_output_zero` | no output, no rent |
| `rent_eq_zero_of_value_zero` | no labour value, no rent |
| `rent_eq_zero_of_wage_zero` | no wage, no rent |
| `rent_mono_markup`, `aggregateRent_mono_markup` | rent rises with the wedge |

The deeper determinants are outside the formalisation but visible in it:
demand inelasticity (the subsistence floor keeps necessity demand at least
`b`, `lesDemand_ge_floor`), barriers to entry (the single-producer condition
must persist), network bottlenecks (single-supplier positions in a sparse
input–output network), and contestability (`μ` must be exercised; a
contestable monopolist with `μ = 0` earns nothing). A full theory would
derive `μ` from demand elasticity and entry costs; here it is exogenous.

## Demand, reproduction and the bottom

`LeanMarx/Demand.lean` adds the population's spending. People have two income
sources,

```
income i = w * labour i + π * capital i,
```

and split income between consumption and investment.

**Subsistence.** A basket `b` is required to reproduce the worker; its cost is
`p · b`. Income below it leaves a reproduction gap and the worker cannot
reproduce.

**Preferences.** Demand is Stone–Geary / linear expenditure:

```
c i = b i + (y − p·b) α i / p i     if y ≥ p·b,
c i = (y / (p·b)) b i               if y < p·b,
```

with `α ≥ 0`, `Σ α = 1`. The floor is bought first, the surplus is spent in
fixed value shares, and below subsistence demand is a rationed multiple of
the basket.

**Investment.** Saving is only possible out of the surplus:
`0 ≤ s ≤ y − p·b`. Consumption is funded by `y − s`, and expenditure plus
saving equals income.

| Result | Statement |
|---|---|
| `canReproduce_iff_gap_nonpos` | reproduction iff the gap is non-positive |
| `below_reproductionWage` | `w < (p·b)/L` ⇒ full-time work is short |
| `canReproduce_iff_labourNeeded_le` | reproduction iff required hours ≤ endowment |
| `labourNeeded_antitone` | capital income substitutes for labour |
| `reproduction_pressure` | income below subsistence ⇒ required hours exceed the endowment |
| `lesDemand_budget_surplus` | above subsistence, demand exhausts income |
| `lesDemand_budget_rationed` | below subsistence, demand still exhausts income |
| `lesDemand_ge_floor` | above subsistence, demand is at least the basket |
| `lesDemand_le_floor_of_rationed` | below subsistence, demand is at most the basket |
| `expenditure_add_saving` | expenditure + saving = income |
| `aggregate_budget` | the same in aggregate |
| `pure_worker_wage_floor` | a pure worker reproduces iff `w ≥ (p·b)/labour` |
| `cannot_reproduce_rationed` | a worker below subsistence is rationed below the basket |

The bottom pressure is the reproduction constraint: for a pure worker,
`w ≥ (p·b)/L`. Below that wage the full labour endowment cannot buy the
subsistence basket, the worker is rationed below `b`, and the required hours
exceed the endowment. This is the mechanism that puts a floor under the wage
and drives distress at the bottom.

The demand system is the standard Stone–Geary/LES form in reduced form; its
properties (budget, floor, rationing, saving) are proved, while the
utility-maximisation problem that generates it is not derived.

## A theory of rent: what determines μ

`LeanMarx/RentTheory.lean` makes rent measurable and gives μ a determination.

**Measurement.** Rent is the normalized distance between price and integrated
labour time:

```
rentRate p v w c = p c / (w · v c) − 1 = (p c − w · v c) / (w · v c).
```

`rentRate_eq_price_gap` states the second form, and `rentRate_eq_of_rate`
says that if the price is `(1 + μ) w v`, the measured gap is exactly μ. So the
price–labour distance *is* the rent rate; nothing unobservable is needed.

**Determination.** A monopolist facing linear demand `q = a − b p` with unit
cost `c = w · v` maximizes `(p − c)(a − b p)`:

| Result | Statement |
|---|---|
| `monopolyProfit_le` | `p* = (a + b c)/(2b)` maximizes profit |
| `monopolyPrice_eq_cost_mul` | `p* = (1 + μ) c` |
| `monopolyMarkup_pos` | μ `> 0` when the market is profitable |
| `monopolyMarkup_antitone_elastic` | more elastic demand (larger `b`) gives smaller μ |
| `monopolyMarkup_eq_inv_elasticity` | `μ = 1/(ε − 1)` at the optimum |
| `determinedMarkup` | the theory-determined μ: monopoly markup or zero |
| `marketPrice_determined` | prices are the monopoly price under one producer, the labour value otherwise |

So two forces determine μ:

1. **Market power / demand.** μ falls with the elasticity of demand and with
   the unit cost, and rises with the size of the market; the Lerner identity
   `μ = 1/(ε − 1)` is the general form.
2. **Contestability / entry.** A second producer removes the monopoly and the
   rent (`rent_eq_zero_of_two_producers`). The observed μ is the monopoly
   markup only where entry is blocked; otherwise it is competed to zero.

The linear-demand model is a tractable instance of the general Lerner logic;
a full theory would add entry costs, bargaining, and dynamics.

### Monopoly and the wage–capital split

Net output splits into wages and rent, and the shares add to one:

```
wageShare = w L / P,        capitalShare = R / P,        wageShare + capitalShare = 1.
```

Because `R = w · V` with `V = Σ_{monopolised c} μ c v c y c`, the wage level
cancels:

```
wageShare = 1 / (1 + V/L),  capitalShare = (V/L) / (1 + V/L).
```

| Result | Statement |
|---|---|
| `netOutputValue_eq` | `P = wL + R` |
| `aggregateRent_eq_w_mul_valueRent` | `R = w · V` |
| `wageShare_add_capitalShare` | the two shares sum to one |
| `wageShare_eq_valueRent` | `wageShare = 1/(1 + V/L)`; `w` cancels |
| `capitalShare_eq_valueRent` | `capitalShare = (V/L)/(1 + V/L)` |
| `wageShare_antitone_valueRent` | more value rent lowers the wage share |
| `valueRentOn_mono_set` | adding a monopolised commodity raises `V` |

So the number of monopolies matters only through the **value-weighted rent**
`V = Σ μ c v c y c`: one large monopoly (high μ, high value weight) can outweigh
many small ones. Adding a monopolised commodity with positive rent raises `V`,
lowers the wage share, and raises the capital share.

### Recovering the average profit rate

The average profit rate is the price difference between total inputs and
product sale, over total input cost:

```
averageProfitRate = (revenue − cost) / cost,
cost = p · (A x) + w · (l · x),   revenue = p · (B x).
```

| Result | Statement |
|---|---|
| `totalRevenue_sub_totalInputCost` | profit = `p·netOutput − w·employment` |
| `averageProfitRate_costPrice` | cost prices leave zero profit |
| `averageProfitRate_eq_of_profitRatePrice` | a Sraffa price with uniform `r`, `p B = (1+r)(p A + w l)`, returns exactly `r` |
| `marketPrice_profit_eq_rent` | at the model's prices, the profit numerator is the rent |
| `averageProfitRate_marketPrice_eq_rent_div` | the rate is rent over total input cost |

Three different numbers must not be conflated:

- the **markup** `μ` (a wedge on labour value);
- the **rent share of net output** `R/(wL+R)`;
- the **profit rate on total capital advanced** `R/(p A x + w l x)`.

They coincide only in special cases: with no produced inputs, `A = 0`, the
markup and the profit rate coincide; in general they do not. A *uniform*
profit rate is recovered from prices satisfying the Sraffa equation; the
model's labour-value markup prices generally do not satisfy it, so the
recovered number is an average over heterogeneous rates, and the
transformation problem reappears in the denominator.

### The profit-rate cross-section

A rate is observed only if the firm survives `M' > M`, i.e. only if `0 < r`.
So the observed cross-section is the underlying rate distribution **truncated
at zero**, with a point mass at failure:

| Result | Statement |
|---|---|
| `failureMass_add_survivorMass` | failure mass plus survival mass is one |
| `survivorMean_ge_overallMean` | selection raises the mean |
| `survivors_filter_eq` | for `t > 0`, survivors above `t` are all firms above `t` |
| `survivor_tail_prob` | conditional tail = unconditional tail count / survival mass |

The expected shape is therefore:

- a **point mass at failure** (`r ≤ 0`): the negative tail is never observed,
  only exit;
- a **right-skewed positive part**: survivors are the `r > 0` truncation;
- an **upper tail inherited** from the rate process: truncation below zero
  rescales the tail but does not change it.

The body is approximately log-normal or Laplace if profit rates are
multiplicative i.i.d. shocks (Gibrat); the firm-size chain gives a Pareto-like
*size* tail when growth is size-dependent (`LeanMarx/FirmSize`). The profit-rate
tail is a separate object and inherits whatever upper tail the rate process
has: thin-tailed shocks give a truncated thin-tailed rate distribution, heavy
shocks give a heavy right tail.

Entry adds a cohort effect. Entrants must cover stocks and labour before the
first sale, so the first-cycle rate is centred near zero or negative and the
entrant failure mass is high. Survivors are selected; the cross-section mixes
young firms (high failure mass, high variance) with old firms (the upper tail).
The capital-allocation rule matters: allocating to entrants with higher
expected rates selects on expected profitability and lowers the entrant failure
mass, but the realised survivor distribution still has a right tail.

The aggregate profit rate is the capital-weighted mean of firm rates; a heavy
upper tail lifts the mean above the median. This is why the aggregate can be
positive while a large fraction of firms fail.

### Income split versus consumption composition

The split above is the split of **income** (wages versus rent). The split of
**consumption** is a further step, and it depends on the demand system:

- With identical Stone–Geary preferences and every agent above subsistence,
  aggregate demand is `N b + (Y − N p·b) α/p`; its composition depends on total
  income, not on its distribution.
- With the non-homothetic floor and rationing, the composition does depend on
  the distribution: richer agents spend a smaller share on necessities. The
  model handles this through the floor and the rationing regime.
- The model does not give workers and capitalists different preference
  parameters, so it does not by itself predict a separate `wage-good` and
  `luxury-good` consumption split; that would need class-specific `(b, α)`.

## Surplus value

With a real wage bundle `b` (goods per unit of labour), the value of labour
power is `v·b` and employment `L` leaves

```
S = L (1 − v·b).
```

`surplusValue_pos_iff`: `S > 0 ↔ v·b < 1`. Surplus value is positive exactly
when the wage is below the value of labour power. It is a claim on the
surplus product, not a price residual.

## Layout

```
LeanMarx/Basic.lean          production table, net output, labour values,
                             existence/uniqueness of values
LeanMarx/Price.lean          dual cost prices, correspondence, no-surplus
LeanMarx/Surplus.lean        value of labour power, surplus value
LeanMarx/Distribution.lean   mixed agents, income shares, Gini bound
LeanMarx/Circuit.lean        one-turn circuit, share and Gini invariance
LeanMarx/Dynamics.lean       balanced growth, iterated circuit, concentration
LeanMarx/Investment.lean     investment, surplus allocation, preferential attachment
LeanMarx/Expectations.lean   investment by expected profit rates
LeanMarx/Selection.lean      producers, bankruptcy, selection
LeanMarx/Startups.lean       startup funding, entry, expected payoff
LeanMarx/Death.lean          Gaussian death probability around the average
LeanMarx/FirmSize.lean       finite growth/death/entry chain, stationary power law
LeanMarx/WealthPump.lean     entry decomposition, active sector, throughput
LeanMarx/SocialMetabolism.lean  labour values, price gaps, rent, supply/demand
LeanMarx/Demand.lean         income, subsistence floors, Stone–Geary demand, saving
LeanMarx/RentTheory.lean     rent measurement, monopoly pricing, determined μ
LeanMarx.lean                library root with overview
LeanMarxDemo.lean            worked tables (single product, joint production)
LeanMarxAudit.lean           #print axioms audit
flake.nix                    elan/Lean 4.35.0 dev shell (flake.lock pins nixpkgs)
lakefile.toml                Mathlib pinned by revision
```

## Assumptions and limits

- Single-period, linear, fixed-coefficient production; no joint production
  restriction, but also no fixed capital, no technical choice, and no
  substitution.
- Labour values are taken to exist and be unique via the rank condition. No
  Perron–Frobenius statement is used or claimed: there is no price-theoretic
  existence theorem for a positive wage or profit rate.
- Cost prices exhaust net output in wages, so a positive profit rate requires
  an added distributional rule; the formalisation stops at the surplus-value
  claim and leaves profit as a parameter.
- The population is finite, so the income distribution is an empirical
  vector; no distributional law (power law, lognormal, etc.) is derived or
  assumed.
- Time is deterministic and discrete: balanced growth, a multiplicative
  circuit, a surplus-allocation investment step, and investment by expected
  profit rates. There are no stochastic shocks, saving behaviour, entry, or
  endogenous profit rates. The limit theorems are concentration of shares
  under a dominant rate and under winner-takes-all.
- Expectations are taken as given. Common expectations are distributionally
  neutral; heterogeneous expectations change shares but no distribution of
  expectations is derived.
- Producers are single-output columns with exogenous profit rates. Bankruptcy
  is a one-period rule (`M' ≤ M`), startups enter with a committed fraction of
  an investor's wealth, and death is a Gaussian probability around the average
  rate. The stationary distribution is derived for a *finite* growth/death/
  entry chain with a specific size-dependent rule; the infinite-population
  limit and the full stochastic process are not derived.
