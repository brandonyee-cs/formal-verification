import PittelMoments

/-! Prints the axioms used by the main theorems of `PittelMoments`. -/

-- Run with `lake env lean Axioms.lean` after `lake build`.
#print axioms PittelSmall.numStableMatchings_eq_countB
#print axioms PittelSmall.expected_eq_sum
#print axioms PittelSmall.secondMoment_eq_sum
#print axioms PittelSmall.card_profile
#print axioms PittelSmall.expected_2_2
#print axioms PittelSmall.secondMoment_2_2
#print axioms PittelSmall.expected_2_3
#print axioms PittelSmall.secondMoment_2_3
#print axioms PittelNTwo.countB_two
#print axioms PittelNTwo.numStableMatchings_two
#print axioms PittelNTwo.numStableMatchings_two_le
#print axioms PittelNTwo.card_C_mul
#print axioms PittelNTwo.expected_two
#print axioms PittelNTwo.secondMoment_two
