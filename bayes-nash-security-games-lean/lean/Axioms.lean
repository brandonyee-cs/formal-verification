import BayesNashSecurityGames

/-! Prints the axioms used by the main theorems of `BayesNashSecurityGames`. -/

-- Run with `lake env lean Axioms.lean` after `lake build`.
#print axioms OMA.BNSG.pairwise_iff_optimal
#print axioms OMA.BNSG.isBayesNash_mkOutput_iff_optimal
#print axioms OMA.BNSG.eq_mkOutput_of_isBayesNash
#print axioms OMA.BNSG.isBayesNash_iff_optimal
#print axioms OMA.BNSG.exists_isBayesNash_of_zero
#print axioms OMA.BNSG.exists_isBayesNash_of_full
#print axioms OMA.BNSG.g₀_valid
#print axioms OMA.BNSG.instance_isBayesNash_family
#print axioms OMA.BNSG.instance_isBayesNash
