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

## The circuit of capital

`LeanMarx/Circuit.lean` adds the minimal one-step circuit: at a uniform
profit rate every investor's capital is scaled by `1 + π`.

| Result | Statement |
|---|---|
| `circuitStep_share` | every investor's share is invariant |
| `gini_smul` | the Gini coefficient is invariant under uniform scaling |
| `circuitStep_exceedance` | `{i | y < (1+π) w i} = {i | y/(1+π) < w i}` |

So the circuit cannot generate a Pareto distribution: it preserves the share
distribution and only relabels thresholds. A power law requires heterogeneity
the circuit does not contain — differential profit rates, idiosyncratic
multiplicative shocks with a reflecting barrier or reset, or a rich-get-richer
mechanism. Independent multiplicative shocks alone (Gibrat) point towards a
lognormal cross-section, not a Pareto one.

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
- There is no dynamics beyond the one-step circuit: no saving, entry,
  differential returns, or stochastic shocks, and no limit theorem.
