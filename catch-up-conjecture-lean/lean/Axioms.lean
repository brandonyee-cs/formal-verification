import CatchUpLean

/-! Prints the axioms used by the main theorems of `CatchUpLean`. -/

-- Run with `lake env lean Axioms.lean` after `lake build`.
-- The conjecture for N ≤ 16, via the certificate checker.
#print axioms CatchUpCert.conj_le_16
#print axioms CatchUpCert.check_sound
#print axioms CatchUpCert.valueAux_eq_D
#print axioms CatchUpCert.value_eq_draw_of_cert
-- The conjecture for N ≤ 12, via the direct evaluator.
#print axioms CatchUpOMA.conj_le_12
#print axioms CatchUpOMA.valueAux_eq_ev
-- The parity lemma, for every N.
#print axioms CatchUpOMA.value_ne_draw_of_odd
#print axioms CatchUpOMA.valueAux_draw_even
