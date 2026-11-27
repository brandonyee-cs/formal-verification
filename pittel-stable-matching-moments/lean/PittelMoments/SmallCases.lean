import FormalConjecturesForMathlib.Combinatorics.StableMarriage.Unbalanced

/-!
Exact small cases of the moments of the number of stable matchings, stated against the
upstream definitions `StableMarriage.Unbalanced.expectedNumStableMatchings` and
`secondMomentNumStableMatchings`. Kernel-checked by `decide` on a computable re-encoding.
-/

namespace PittelSmall

open StableMarriage.Unbalanced

/-- Boolean stability of a function, the same condition as `IsStable`. -/
def isStableB {n m : ℕ} (p : Profile n m) (μ : Fin n → Fin m) : Bool :=
  decide (∀ i j, ¬ (μ i ≠ j ∧ p.firmRank i j < p.firmRank i (μ i) ∧
    ∀ k, μ k = j → p.workerRank j i < p.workerRank j k))

/-- Computable count of stable matchings, enumerating injective functions. -/
def countB {n m : ℕ} (p : Profile n m) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin m => Function.Injective f ∧ isStableB p f = true)).card

theorem numStableMatchings_eq_countB {n m : ℕ} (p : Profile n m) :
    numStableMatchings p = countB p := by
  classical
  unfold numStableMatchings countB
  rw [← Fintype.card_subtype]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun μ => ⟨μ.1, μ.1.injective, by
        have h := μ.2
        simp only [IsStable, IsBlockingPair] at h
        simpa [isStableB] using h⟩
      invFun := fun f => ⟨⟨f.1, f.2.1⟩, by
        have h := f.2.2
        simp only [isStableB, decide_eq_true_eq] at h
        simpa [IsStable, IsBlockingPair] using h⟩
      left_inv := fun μ => rfl
      right_inv := fun f => rfl }

theorem expected_eq_sum (n m : ℕ) :
    expectedNumStableMatchings n m =
      ((∑ p : Profile n m, countB p : ℕ) : ℝ) / (Fintype.card (Profile n m) : ℝ) := by
  unfold expectedNumStableMatchings uniformProfile
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, numStableMatchings_eq_countB, Nat.cast_sum]
  rw [← Finset.mul_sum, div_eq_inv_mul]

theorem secondMoment_eq_sum (n m : ℕ) :
    secondMomentNumStableMatchings n m =
      ((∑ p : Profile n m, countB p ^ 2 : ℕ) : ℝ) / (Fintype.card (Profile n m) : ℝ) := by
  unfold secondMomentNumStableMatchings uniformProfile
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, numStableMatchings_eq_countB, Nat.cast_sum, Nat.cast_pow]
  rw [← Finset.mul_sum, div_eq_inv_mul]

theorem card_profile (n m : ℕ) :
    Fintype.card (Profile n m) = (m.factorial) ^ n * (n.factorial) ^ m := by
  rw [Fintype.card_congr
    ({ toFun := fun p => (p.firmRank, p.workerRank)
       invFun := fun p => ⟨p.1, p.2⟩
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } :
      Profile n m ≃ (Fin n → Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin n)))]
  simp [Fintype.card_perm]

theorem sum_2_2 : (∑ p : Profile 2 2, countB p) = 18 := by decide
theorem sum_sq_2_2 : (∑ p : Profile 2 2, countB p ^ 2) = 22 := by decide

theorem expected_2_2 : expectedNumStableMatchings 2 2 = 9 / 8 := by
  rw [expected_eq_sum, sum_2_2, card_profile]; norm_num [Nat.factorial]

theorem secondMoment_2_2 : secondMomentNumStableMatchings 2 2 = 11 / 8 := by
  rw [secondMoment_eq_sum, sum_sq_2_2, card_profile]; norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
theorem sum_2_3 : (∑ p : Profile 2 3, countB p) = 300 := by decide
set_option maxRecDepth 100000 in
theorem sum_sq_2_3 : (∑ p : Profile 2 3, countB p ^ 2) = 324 := by decide

/-- One extra worker, two firms: `E[S] = 25/24`. -/
theorem expected_2_3 : expectedNumStableMatchings 2 3 = 25 / 24 := by
  rw [expected_eq_sum, sum_2_3, card_profile]; norm_num [Nat.factorial]

/-- One extra worker, two firms: `E[S^2] = 9/8`. -/
theorem secondMoment_2_3 : secondMomentNumStableMatchings 2 3 = 9 / 8 := by
  rw [secondMoment_eq_sum, sum_sq_2_3, card_profile]; norm_num [Nat.factorial]

end PittelSmall
