import RoommatesThreshold

/-!
Prints the axioms used by the main theorems.
Run with `lake env lean Axioms.lean` after `lake build`.
-/

#print axioms RoommatesThreshold.stabilityThreshold_le_half
#print axioms RoommatesThreshold.stabilityThreshold_mono
#print axioms RoommatesThreshold.K3
#print axioms RoommatesThreshold.K4
#print axioms RoommatesThreshold.K5
#print axioms RoommatesThreshold.K6
#print axioms RoommatesThreshold.three_le_K
#print axioms RoommatesThreshold.target_of_lowerBound
