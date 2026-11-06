import LeanMarx

/-! Axiom audit for the main results. Run `lake env lean LeanMarxAudit.lean`. -/

#print axioms LeanMarx.exists_labourValue
#print axioms LeanMarx.unique_labourValue
#print axioms LeanMarx.ProductionTable.existsUnique_labourValue
#print axioms LeanMarx.ProductionTable.value_netOutput
#print axioms LeanMarx.ProductionTable.costPrice_of_labourValue
#print axioms LeanMarx.ProductionTable.costPrice_eq_smul_labourValue
#print axioms LeanMarx.ProductionTable.costPrice_exists_iff
#print axioms LeanMarx.ProductionTable.costPrice_wage_value_of_labour_power
#print axioms LeanMarx.ProductionTable.surplusValue_pos_iff
#print axioms LeanMarx.Population.incomeShare_eq_mixture
#print axioms LeanMarx.Population.incomeShare_eq_labourShare_of_proportional
#print axioms LeanMarx.Population.incomeShare_of_pure_worker
#print axioms LeanMarx.Population.wageShareOfIncome_nonneg
#print axioms LeanMarx.gini_mixture_le
#print axioms LeanMarx.circuitStep_share
#print axioms LeanMarx.gini_smul
#print axioms LeanMarx.circuitStep_exceedance
