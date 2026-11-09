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
import LeanMarx.FirmSize
import LeanMarx.WealthPump
import LeanMarx.SocialMetabolism
import LeanMarx.Demand
import LeanMarx.RentTheory
import LeanMarx.Shares

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

## 9. Stationary firm sizes (`LeanMarx/FirmSize`)

A finite growth/death/entry chain on sizes `{0, …, N}` has an explicit
stationary distribution. With the size-dependent growth probability
`g k = ((k+1)/(k+2))^α`, the stationary masses are `π k ∝ (k+1)^{-α}`: a
power law. The mass ratio tends to one, unlike a geometric distribution whose
ratio is a constant below one. With one firm per investor this is the
stationary wealth distribution.

## 10. The wealth pump and entry (`LeanMarx/WealthPump`)

The stationary masses factor as `π k = e A k / (1 + e Σ A)`. Entry is the
extensive margin: a fall in entry raises the zero-wealth mass, shrinks the
active sector and lowers the gross flow up the ladder, while leaving the
conditional distribution among active firms and the Pareto exponent
unchanged. The pump's intensity is set by the size dependence of growth and
death, not by entry.

## 11. Social metabolism: labour, price and rent (`LeanMarx/SocialMetabolism`)

Two numbers per commodity: labour value `v c` (recursive embodiment
`v B = l + v A`) and market price `p c`. A rent wedge is available only to a
single producer of a commodity: `p c = (1 + μ c) w v c` under monopoly,
`p c = w v c` otherwise. `μ > 0` is monopoly rent, `μ < 0` monopsony rent.
The aggregate identity is `P = w L + R`, and `R` is zero exactly when no
commodity is monopolised.

## 12. Demand, reproduction and the bottom (`LeanMarx/Demand`)

People earn from labour and capital, then split income between consumption
and investment. A subsistence basket `b` has cost `p·b`; income below it
means the worker cannot reproduce. Preferences are Stone–Geary: buy `b`
first, then spend the surplus in value shares; below subsistence demand is a
rationed multiple of `b`. Saving is only possible out of the surplus, and
expenditure plus saving equals income, individually and in aggregate. For a
pure worker reproduction requires `w ≥ (p·b)/labour`, the wage floor that
puts pressure on the bottom.

## 13. A theory of rent (`LeanMarx/RentTheory`)

Rent is the price–labour distance: `p/(w·v) − 1`, and the gap recovers μ.
For μ itself, monopoly pricing with linear demand gives
`p* = (a + b c)/(2b)` and `μ = (a − b c)/(2 b c)`, equivalently
`μ = 1/(ε − 1)` at the profit-maximising price. More elastic demand gives a
smaller μ; competition (two or more producers) gives zero. So market power
sets the potential μ and contestability decides whether it survives.

## 14. The wage–capital split (`LeanMarx/Shares`)

`P = w L + R` splits net output into `wageShare = wL/P` and
`capitalShare = R/P`, which sum to one. Writing
`V = Σ_{monopolised c} μ c v c y c` for the value-weighted rent,

```
wageShare = 1 / (1 + V/L),      capitalShare = (V/L) / (1 + V/L).
```

The wage level cancels: the split is set by value-weighted rent per unit of
labour, not by the number of monopolies as such. More or larger monopolies
raise `V` and lower the wage share; one large monopoly can outweigh many
small ones.

## 15. Surplus value (`LeanMarx/Surplus`)

`S = L (1 − v·b)`: employment less the labour embodied in the real wage. It
is positive exactly when the value of labour power is below one. Profit is a
distributional claim on `S`, not a price residual.
-/
