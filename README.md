# lean-marx

Two classical questions of linear Marxian economics, formalised in Lean 4
against Mathlib.

1. **What does it take for prices to correspond to labour values?**
   `LeanMarx/Correspondence.lean`
2. **How is income distributed between workers and capitalists when everyone
   may be a mixture of the two?** `LeanMarx/Distribution.lean`

The two meet in `LeanMarx/Fundamental.lean`: when the correspondence holds,
money profit is proportional to surplus value and the money profit rate is the
value rate of profit.

## Building

The toolchain comes from Nix; Mathlib is pinned by revision in
`lakefile.toml`.

```bash
nix develop -c lake exe cache get   # prebuilt Mathlib oleans
nix develop -c lake build
```

`nix develop` supplies Lean 4.35.0 (`lean`, `lake`) from nixpkgs, pinned by
`flake.lock`. The first `lake exe cache get` fetches Mathlib at the revision
in `lakefile.toml` and unpacks its cache; without it the first build compiles
Mathlib from source.

An audit of the axioms used by the main results:

```bash
nix develop -c lake env lean LeanMarxAudit.lean
```

## Model

A single-product (Leontief/Sraffa) economy over a finite sector set:

- `A i j` — units of commodity `j` consumed per unit of commodity `i`;
- `l i` — direct labour per unit of gross output of `i`;
- Leontief matrix `I − A`, productive when its determinant is a unit;
- **labour values** `v = l (I − A)⁻¹`, so `v (I − A) = l`.

**Prices of production** (`LeanMarx.Price`): a price vector `p`, profit rate
`r` and money wage `w` satisfy `p = (1 + r) (p A + w l)`. Dotting against
gross output `x` yields the aggregate identities used for distribution:

- profit `Π = p (I − A) x − w L = r (p A x + w L)`;
- wage share `Z / (Z + Π) = 1 / (1 + r (1 + c))`, `c = p A x / (w L)`.

## Feature 1 — a labour correspondence with prices

All results are in `LeanMarx.Correspondence` (with `r ≠ 0` and
`I − (1+r)A` invertible where prices are solved for):

| Result | Statement |
|---|---|
| Zero profit | `r = 0` implies `p = w v`: prices are always proportional to values. |
| **Criterion** | `p ∝ v  ↔  v ∝ l`. |
| **Equal organic composition** | `v ∝ l  ↔  ∃ μ, l A = μ l`. |

So a labour correspondence exists exactly when the direct labour vector is a
**left eigenvector of the input–output matrix**, i.e. when every sector has
the same organic composition of capital. It is a property of the technology,
not of the price level; at a zero profit rate it is automatic, and with
profit it can fail. The multiplier is explicit: if `v = c l` then prices
satisfy `p = ((1+r)w / (λ c)) v` with `λ = 1 − (1+r)(1 − 1/c)`.

`LeanMarxDemo.lean` works two two-sector examples:

- `equalE` — symmetric matrix, `l = (1,1)`, equal organic composition; labour
  values are `(4,4)`, the criterion produces the price vector `(20,20)` at
  `r = 1/4`, `w = 1`, and `(20,20) = 5 · (4,4)`.
- `unequalE` — upper-triangular matrix, `l = (1,0)`, labour values `(2,2)`;
  the criterion proves that **no** price system with nonzero profit rate is
  proportional to values.

## Feature 2 — income distribution with mixed agents

`LeanMarx.Distribution` models a population in which agent `i` owns labour
`ℓ i` and capital `k i`. At wage rate `w` and profit rate `π`:

```
y i = w · ℓ i + π · k i,        s i = y i / Σ y.
```

The structural result is that every income share is a convex combination of
the agent's labour share and capital share, with weights the economy-wide
wage and profit shares:

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

In the price system of `LeanMarx.Price` the economy-wide wage share is
`1 / (1 + r (1 + c))`, strictly decreasing in the profit rate `r`. That is the
mixture weight `ω` when the population's capital is the capital advanced by
the economy — materials `p A x` together with the wage fund `w L`, so that
profit is `r (p A x + w L)` and total income is the price of net output (see
the assumptions section). Then the distribution is predicted by the profit
rate and capital intensity, and each agent's position is a mixture of the two
class shares.

## Bridge — profit and surplus value

`LeanMarx.Fundamental` takes a wage bundle `b` (goods per unit of labour) and
the correspondence `p = k v`:

- profit `Π = k · S`, where `S = L (1 − v·b)` is surplus value;
- `S > 0 ↔ v·b < 1` (positive exploitation);
- the money profit rate equals the value rate of profit
  `r = S / (C + V)` with `C = v·A x`, `V = (v·b) L`.

Thus the price-based distribution of feature 2 is the value-based exploitation
accounting of feature 1 exactly when the labour correspondence holds.

## Layout

```
LeanMarx/Basic.lean          economy, Leontief inverse, labour values
LeanMarx/Price.lean          Sraffa price system, profit, wage share
LeanMarx/Correspondence.lean criterion p ∝ v ↔ v ∝ l, eigenvector form
LeanMarx/Distribution.lean   mixed agents, income shares, Gini bound
LeanMarx/Fundamental.lean    profit = k · surplus value, value profit rate
LeanMarx.lean                library root with overview
LeanMarxDemo.lean            worked examples (positive and negative)
LeanMarxAudit.lean           #print axioms audit
flake.nix                    Lean 4.35.0 dev shell (flake.lock pins nixpkgs)
lakefile.toml                Mathlib pinned by revision
```

## Assumptions and limits

- Single-product linear economy; no joint production, fixed capital or
  technical choice, so labour values are unique when `I − A` is invertible.
- The criterion takes prices as given solutions of the Sraffa system. The
  existence of a positive price vector and profit rate for an arbitrary
  nonnegative `A` is a Perron–Frobenius statement that Mathlib does not yet
  provide; it is not needed for the equivalence, which is algebraic.
- `Proportional` is defined with a nonzero scalar, not a positive one, so the
  theorems hold even when prices are negative; adding `0 < c` recovers the
  economic reading.
- Prices are assumed to be paid from capital advanced (wages enter the
  markup), as in Sraffa; this is what makes the wage share
  `1 / (1 + r (1 + c))`.
- The distribution model leaves `w` and `π` as parameters. Identifying the
  population's aggregate capital with the economy's capital advanced
  (`p A x + w L`) is a modelling step, not a theorem; under it the mixture
  weight `ω` is the Sraffa wage share.
