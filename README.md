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
  is a one-period rule (`M' ≤ M`), and startups enter with a committed
  fraction of an investor's wealth. There is no stochastic distribution of
  startup outcomes or growth, so no stationary firm-size distribution is
  derived.
