import LeanMarx.Basic
import LeanMarx.Price
import LeanMarx.Surplus
import LeanMarx.Distribution
import LeanMarx.Circuit
import LeanMarx.Dynamics

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

## 4. Surplus value (`LeanMarx/Surplus`)

`S = L (1 − v·b)`: employment less the labour embodied in the real wage. It
is positive exactly when the value of labour power is below one. Profit is a
distributional claim on `S`, not a price residual.
-/
