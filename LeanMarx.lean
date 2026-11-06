import LeanMarx.Basic
import LeanMarx.Price
import LeanMarx.Surplus
import LeanMarx.Distribution
import LeanMarx.Circuit
import LeanMarx.Dynamics
import LeanMarx.Investment
import LeanMarx.Expectations
import LeanMarx.Selection
import LeanMarx.Startups
import LeanMarx.Death

/-!
# Marxian economics in Lean 4: production tables, prices, distribution

The economy is an input–output **production table**: a use matrix `A`, a make
matrix `B` (joint production allowed), and labour `l` as an input row. The
net-output operator is `N = B − A`.

## 1. When is there a labour correspondence with prices?
(`LeanMarx.Basic`, `LeanMarx.Price`)

* Labour values are the vectors `v` with `v N = l`.
* With joint production `N` need not be invertible: `ValuesExist` (a left
  inverse) gives a value for every labour input, `ValuesUnique` (a right
  inverse) makes it unique. Both are `N` invertible.
* Prices are the **dual cost prices** of the table: `p N = w l`. There is no
  Sraffa markup. Prices exist exactly when labour values do, and when values
  are unique every cost price is `w • v`: the correspondence is a theorem.
* With cost prices and a wage equal to the price of the real wage bundle, the
  value of labour power is one — cost prices leave no surplus.

## 2. Income distribution of mixed worker–capitalist agents
(`LeanMarx.Distribution`)

Each agent owns labour and capital, so is a mixture of the two classes.
Income shares are convex combinations of labour and capital shares with the
wage and profit shares as weights; the Gini coefficient of income is bounded
by the weighted average of the component Ginis.

## 3. Time (`LeanMarx.Circuit`, `LeanMarx.Dynamics`)

Activities can grow along a balanced path `x (t+1) = (1+g) x t`, with
employment and the money value of net output growing at `1+g` while labour
values and cost prices stay put. Investor capital follows the circuit
`w (t+1) i = (1+π i) w t i`, solved by `w t i = (1+π i)^t w0 i`.

Equal rates preserve every share and the Gini coefficient at every date.
Differential rates concentrate: the dominant rate's share tends to one, so
the circuit cannot create a Pareto law — it either preserves the initial
distribution or collapses it to a point mass.

## 4. Investment and preferential attachment (`LeanMarx.Investment`)

Agents invest capital; a period's surplus `π K` is distributed by an
allocation rule. Proportional allocation is scale-invariant and preserves
expected shares. A strictly preferential rule raises the favoured agent's
share, and winner-takes-all drives the winner's share to one. A power law
over agents needs entry, not just preferential allocation among a fixed set.

## 5. Expected profit rates (`LeanMarx/Expectations`)

Investors allocate capital across activities in proportion to expected
profit rates. Aggregate investment into an activity is independent of the
wealth distribution; when all investors share the same expectations, every
capital is multiplied by the same rate-weighted average, so shares and the
Gini coefficient are invariant. Differences in wealth shares come from
heterogeneous expectations: above-average expected returns gain share.

## 6. Producers and bankruptcy (`LeanMarx/Selection`)

A producer is a column making one indexed commodity; several producers may
make the same commodity. A producer survives only if `M' > M`; otherwise it
goes bankrupt (`M' ≤ M`, i.e. `r ≤ 0`). Failing producers' capital decays to
zero, and a strictly dominant producer takes the whole share. Exit is the
missing ingredient for firm-dynamics power laws, but deterministic selection
alone still concentrates.

## 7. Startups (`LeanMarx/Startups`)

Investors found new producers with a fraction of their wealth. A startup is
subject to the same rule, `M' > M`: it returns `+c r` on success, loses the
committed capital `c` on failure, and is worth founding exactly when the
expected gross return satisfies `1 < p (1 + r)`. Entry adjoins a new producer
index set, and the same exit rule applies to old producers and startups
together.

## 8. Stochastic death (`LeanMarx/Death`)

Death is a probability, not a rule: a producer's rate is compared with the
capital-weighted average `r̄`, and the death probability is the lower tail of a
Gaussian centred at `r̄`, `Φ((r̄ - r)/σ)`. It is a probability in `[0,1]`,
antitone in the rate, `1/2` at the average, above `1/2` below it and below
`1/2` above it. Deviations from the average sum to zero, and expected growth
is increasing in the rate. A stationary power law still needs a full
stochastic process with entry; the module supplies the death rule and the
one-period selection inequalities.

## 9. Surplus value (`LeanMarx/Surplus`)

`S = L (1 − v·b)`: employment less the labour embodied in the real wage. It
is positive exactly when the value of labour power is below one. Profit is a
distributional claim on `S`, not a price residual.
-/
