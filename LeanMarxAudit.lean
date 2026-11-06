import LeanMarx

/-! Axiom audit for the main results. Run `lake env lean LeanMarxAudit.lean`. -/

#print axioms LeanMarx.Economy.price_value_of_zero_profit
#print axioms LeanMarx.Economy.price_proportional_value_iff
#print axioms LeanMarx.Economy.value_proportional_labour_iff_leftEigen
#print axioms LeanMarx.Economy.wageShare_eq
#print axioms LeanMarx.Economy.wageShare_strictAnti
#print axioms LeanMarx.Population.incomeShare_eq_mixture
#print axioms LeanMarx.Population.wageShare_add_profitShare
#print axioms LeanMarx.Population.wageShareOfIncome_nonneg
#print axioms LeanMarx.Population.profitShareOfIncome_nonneg
#print axioms LeanMarx.Population.incomeShare_eq_labourShare_of_proportional
#print axioms LeanMarx.Population.incomeShare_of_pure_worker
#print axioms LeanMarx.gini_mixture_le
#print axioms LeanMarx.Economy.profit_eq_surplusValue
#print axioms LeanMarx.Economy.profitRate_eq_valueProfitRate
