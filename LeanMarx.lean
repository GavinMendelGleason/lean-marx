import LeanMarx.Basic
import LeanMarx.Price
import LeanMarx.Correspondence
import LeanMarx.Distribution
import LeanMarx.Fundamental

/-!
# Marxian economics in Lean 4

A formal development of two questions in linear Marxian economics.

## 1. A labour correspondence with prices (`LeanMarx.Correspondence`)

For a single-product economy with input–output matrix `A` and labour vector
`l`, labour values are `v = l (I − A)⁻¹`. Prices of production solve the
Sraffa system `p = (1+r)(p A + w l)`.

* At zero profit rate, `p = w v`: prices are always proportional to values.
* At a nonzero profit rate, `p ∝ v` **iff** `v ∝ l`, i.e. **iff** `l` is a
  left eigenvector of `A` (equal organic composition of capital).

## 2. Income distribution of mixed worker–capitalist agents
(`LeanMarx.Distribution`)

Each agent owns labour and capital, so every agent is a mixture of the two
classes. Income shares are convex combinations of labour and capital shares,
weighted by the economy-wide wage and profit shares. The wage share is
`1 / (1 + r (1 + c))`, where `c` is capital intensity, and it falls with the
profit rate. Mixing two distributions never raises the Gini coefficient above
the weighted average of the components'.

## Bridge (`LeanMarx.Fundamental`)

Under the correspondence, profit is `k` times surplus value and the money
profit rate equals the value rate of profit `S / (C + V)`.
-/
