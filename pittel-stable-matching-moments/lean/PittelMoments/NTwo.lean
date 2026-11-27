import FormalConjecturesForMathlib.Combinatorics.StableMarriage.Unbalanced

/-!
Two firms, any number `m ≥ 2` of workers: exact first and second moments of the number of
stable matchings, stated against the upstream definitions
`StableMarriage.Unbalanced.expectedNumStableMatchings` and `secondMomentNumStableMatchings`:
`E[S] = 1 + 1/(4m(m-1))` and `E[S^2] = 1 + 3/(4m(m-1))`.

The proof is structural (see PROOF.md): for `m ≥ 2` (profiles `Profile 2 (k+2)`) every profile
has one or two stable matchings, two exactly on the event `C`, and `C` is counted by explicit
bijections. `decide` is used only on `Fin 2` and `Perm (Fin 2)`. For `m < 2` there is no injection
`Fin 2 ↪ Fin m`, so the count is `0`; that case is not covered by these theorems.
-/

namespace PittelNTwo

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

/-! ## Two firms: structure of the stable set -/

theorem not_lt_fin_two_perm (r : Equiv.Perm (Fin 2)) : ¬ (r 0 < r 1) ↔ r 1 < r 0 := by
  have hne : r 0 ≠ r 1 := fun h => absurd (r.injective h) (by decide)
  constructor
  · intro h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  · intro h h'; exact lt_asymm h h'

/-- Worker `w` prefers firm `1` to firm `0`. -/
def prefB {m : ℕ} (p : Profile 2 m) (w : Fin m) : Prop := p.workerRank w 1 < p.workerRank w 0

instance {m : ℕ} (p : Profile 2 m) (w : Fin m) : Decidable (prefB p w) := by
  unfold prefB; infer_instance

theorem isStableB_two_iff {m : ℕ} (p : Profile 2 m) (f : Fin 2 → Fin m) :
    isStableB p f = true ↔
      (∀ j, p.firmRank 0 j < p.firmRank 0 (f 0) → j = f 1 ∧ prefB p j) ∧
      (∀ j, p.firmRank 1 j < p.firmRank 1 (f 1) → j = f 0 ∧ ¬ prefB p j) := by
  simp only [isStableB, decide_eq_true_eq, Fin.forall_fin_two]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hj0 : f 0 ≠ j := fun h => by subst h; exact lt_irrefl _ hj
      by_cases hj1 : f 1 = j
      · refine ⟨hj1.symm, ?_⟩
        by_contra hp
        apply h0 j
        refine ⟨hj0, hj, fun h => absurd h hj0, fun _ => ?_⟩
        by_contra h'
        exact hp ((not_lt_fin_two_perm _).mp h')
      · exact absurd ⟨hj0, hj, fun h => absurd h hj0, fun h => absurd h hj1⟩ (h0 j)
    · have hj1 : f 1 ≠ j := fun h => by subst h; exact lt_irrefl _ hj
      by_cases hj0 : f 0 = j
      · refine ⟨hj0.symm, ?_⟩
        intro hp
        apply h1 j
        exact ⟨hj1, hj, fun _ => hp, fun h => absurd h hj1⟩
      · exact absurd ⟨hj1, hj, fun h => absurd h hj0, fun h => absurd h hj1⟩ (h1 j)
  · rintro ⟨h0, h1⟩
    refine ⟨fun j ⟨_, hlt, _, hk1⟩ => ?_, fun j ⟨_, hlt, hk0, _⟩ => ?_⟩
    · obtain ⟨rfl, hp⟩ := h0 j hlt
      exact lt_asymm hp (hk1 rfl)
    · obtain ⟨rfl, hp⟩ := h1 j hlt
      exact hp (hk0 rfl)


section
variable {k : ℕ}

theorem fin_zero_ne_one' : (0 : Fin (k+2)) ≠ 1 := by
  simp

theorem forall_lt_symm_zero (r : Equiv.Perm (Fin (k+2))) (R : Fin (k+2) → Prop) :
    (∀ j, r j < r (r.symm 0) → R j) := by
  intro j h; rw [Equiv.apply_symm_apply] at h; exact absurd h (Fin.not_lt_zero _)

theorem forall_lt_symm_one_iff (r : Equiv.Perm (Fin (k+2))) (R : Fin (k+2) → Prop) :
    (∀ j, r j < r (r.symm 1) → R j) ↔ R (r.symm 0) := by
  rw [Equiv.apply_symm_apply]
  constructor
  · intro h; apply h; rw [Equiv.apply_symm_apply, Fin.lt_def, Fin.val_one]; simp
  · intro h j hj
    have h0 : r j = 0 := by
      rw [Fin.lt_def, Fin.val_one] at hj; exact Fin.ext (by rw [Fin.val_zero]; omega)
    have : j = r.symm 0 := (Equiv.eq_symm_apply r).mpr h0
    subst this; exact h

theorem mem_top_two (r : Equiv.Perm (Fin (k+2))) (x y : Fin (k+2)) (P : Fin (k+2) → Prop)
    (h : ∀ j, r j < r x → j = y ∧ P j) : x = r.symm 0 ∨ x = r.symm 1 := by
  rcases Nat.lt_or_ge (r x).val 2 with hx | hx
  · rcases (by omega : (r x).val = 0 ∨ (r x).val = 1) with h0 | h1
    · left; rw [Equiv.eq_symm_apply]; exact Fin.ext (by simp [h0])
    · right; rw [Equiv.eq_symm_apply]; exact Fin.ext (by simp [h1])
  · exfalso
    have e0 := (h (r.symm 0) (by
      rw [Equiv.apply_symm_apply, Fin.lt_def, Fin.val_zero]; omega)).1
    have e1 := (h (r.symm 1) (by
      rw [Equiv.apply_symm_apply, Fin.lt_def, Fin.val_one]; omega)).1
    exact fin_zero_ne_one' (r.symm.injective (e0.trans e1.symm))

theorem injective_fin_two_iff {α : Type*} (x y : α) : Function.Injective ![x, y] ↔ x ≠ y := by
  constructor
  · intro h e
    have := @h 0 1 (by simp [e])
    exact absurd this (by decide)
  · intro hne a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

/-- The four candidate matchings: firm 0 gets its top or second choice, likewise firm 1. -/
def cand (p : Profile 2 (k+2)) (ij : Fin 2 × Fin 2) : Fin 2 → Fin (k+2) :=
  ![(p.firmRank 0).symm (if ij.1 = 0 then 0 else 1), (p.firmRank 1).symm (if ij.2 = 0 then 0 else 1)]

theorem cand_injective (p : Profile 2 (k+2)) : Function.Injective (cand p) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [cand, Matrix.cons_val_zero, Matrix.cons_val_one, Equiv.apply_eq_iff_eq] at h0 h1
  have hz := (fin_zero_ne_one' (k := k))
  fin_cases i <;> fin_cases i' <;> fin_cases j <;> fin_cases j' <;> simp_all [eq_comm]

theorem countB_eq_sum_cand (p : Profile 2 (k+2)) :
    countB p = ∑ ij : Fin 2 × Fin 2,
      if (Function.Injective (cand p ij) ∧ isStableB p (cand p ij) = true) then 1 else 0 := by
  unfold countB
  rw [Finset.card_filter]
  calc (∑ f : Fin 2 → Fin (k+2), if (Function.Injective f ∧ isStableB p f = true) then 1 else 0)
      = ∑ f ∈ Finset.univ.image (cand p),
          if (Function.Injective f ∧ isStableB p f = true) then 1 else 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro f _ hf
        rw [if_neg]
        rintro ⟨hi, hs⟩
        apply hf
        have hne : f 0 ≠ f 1 := fun e => absurd (hi e) (by decide)
        obtain ⟨h0, h1⟩ := (isStableB_two_iff p f).mp hs
        have c0 := mem_top_two (p.firmRank 0) (f 0) (f 1) _ h0
        have c1 := mem_top_two (p.firmRank 1) (f 1) (f 0) _ h1
        rw [Finset.mem_image]
        have hf' : f = ![f 0, f 1] := by
          funext t; fin_cases t <;> rfl
        rcases c0 with e0 | e0 <;> rcases c1 with e1 | e1
        · exact ⟨(0, 0), Finset.mem_univ _, by rw [hf', e0, e1]; simp [cand]⟩
        · exact ⟨(0, 1), Finset.mem_univ _, by rw [hf', e0, e1]; simp [cand]⟩
        · exact ⟨(1, 0), Finset.mem_univ _, by rw [hf', e0, e1]; simp [cand]⟩
        · exact ⟨(1, 1), Finset.mem_univ _, by rw [hf', e0, e1]; simp [cand]⟩
    _ = _ := Finset.sum_image (fun x _ y _ h => cand_injective p h)


theorem injective_fin_two_iff' {α : Type*} (f : Fin 2 → α) : Function.Injective f ↔ f 0 ≠ f 1 := by
  constructor
  · intro h e
    exact absurd (h e) (by decide)
  · intro hne a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]

theorem valid_iff (p : Profile 2 (k+2)) (f : Fin 2 → Fin (k+2)) :
    (Function.Injective f ∧ isStableB p f = true) ↔ f 0 ≠ f 1 ∧
      ((∀ j, p.firmRank 0 j < p.firmRank 0 (f 0) → j = f 1 ∧ prefB p j) ∧
      (∀ j, p.firmRank 1 j < p.firmRank 1 (f 1) → j = f 0 ∧ ¬ prefB p j)) := by
  rw [injective_fin_two_iff', isStableB_two_iff]

theorem forall_lt_symm_zero_iff (r : Equiv.Perm (Fin (k+2))) (R : Fin (k+2) → Prop) :
    (∀ j, r j < r (r.symm 0) → R j) ↔ True :=
  iff_true_intro (forall_lt_symm_zero r R)

theorem forall_eq_zero_iff (r : Equiv.Perm (Fin (k+2))) (R : Fin (k+2) → Prop) :
    (∀ j, r j = 0 → R j) ↔ R (r.symm 0) := by
  constructor
  · intro h; exact h _ (Equiv.apply_symm_apply r 0)
  · intro h j hj
    have : j = r.symm 0 := (Equiv.eq_symm_apply r).mpr hj
    subst this; exact h

/-- The event that there are two stable matchings. -/
def C (p : Profile 2 (k+2)) : Prop :=
  (p.firmRank 0).symm 0 = (p.firmRank 1).symm 1 ∧ (p.firmRank 1).symm 0 = (p.firmRank 0).symm 1 ∧
    prefB p ((p.firmRank 0).symm 0) ∧ ¬ prefB p ((p.firmRank 1).symm 0)

instance (p : Profile 2 (k+2)) : Decidable (C p) := by unfold C; infer_instance

theorem arith_two {m : ℕ} (a0 a1 b0 b1 : Fin m) (PA PB : Prop) [Decidable PA] [Decidable PB]
    (hA : a0 ≠ a1) (hB : b0 ≠ b1) (hP : a0 = b0 → (PA ↔ PB)) :
    ((if a0 = b0 then 0 else 1) + (if ¬a0 = b1 ∧ b0 = a0 ∧ ¬PB then 1 else 0)) +
      ((if ¬a1 = b0 ∧ a0 = b0 ∧ PA then 1 else 0) +
        (if ¬a1 = b1 ∧ (a0 = b1 ∧ PA) ∧ b0 = a1 ∧ ¬PB then 1 else 0)) =
      (if a0 = b1 ∧ b0 = a1 ∧ PA ∧ ¬PB then 2 else 1) := by
  by_cases h0 : a0 = b0
  · subst h0
    have hP' := hP rfl
    by_cases hPB : PB
    · have : PA := hP'.mpr hPB
      simp [hPB, this, hA, Ne.symm hA, hB]
    · have : ¬PA := fun h => hPB (hP'.mp h)
      simp [hPB, this, hA, Ne.symm hA, hB]
  · by_cases h1 : a0 = b1 <;> by_cases h2 : b0 = a1 <;> by_cases hPA : PA <;> by_cases hPB : PB <;>
      simp [h0, Ne.symm h0, h1, h2, hPA, hPB, hA, hB] <;> grind

/-- For `m = k + 2 ≥ 2` workers, the count is `2` on `C` and `1` otherwise. -/
theorem countB_two (p : Profile 2 (k+2)) : countB p = if C p then 2 else 1 := by
  rw [countB_eq_sum_cand, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, valid_iff]
  simp [cand]
  simp only [forall_eq_zero_iff]
  unfold C
  have hA : (p.firmRank 0).symm 0 ≠ (p.firmRank 0).symm 1 :=
    fun e => fin_zero_ne_one' ((p.firmRank 0).symm.injective e)
  have hB : (p.firmRank 1).symm 0 ≠ (p.firmRank 1).symm 1 :=
    fun e => fin_zero_ne_one' ((p.firmRank 1).symm.injective e)
  exact arith_two _ _ _ _ _ _ hA hB (fun h => by rw [h])



/-- Upstream form: with two firms and `m = k + 2 ≥ 2` workers there are one or two stable
matchings, two exactly on the event `C`. (For `m < 2` the count is `0`; not covered here.) -/
theorem numStableMatchings_two (p : Profile 2 (k+2)) :
    numStableMatchings p = if C p then 2 else 1 := by
  rw [numStableMatchings_eq_countB, countB_two]

theorem numStableMatchings_two_le (p : Profile 2 (k+2)) : numStableMatchings p ≤ 2 := by
  rw [numStableMatchings_two]; split_ifs <;> omega

end

/-! ## Counting -/

section
variable {k : ℕ}

/-- Number of permutations with prescribed values at `0` and `1`. -/
def F (c d : Fin (k+2)) : ℕ :=
  (Finset.univ.filter (fun τ : Equiv.Perm (Fin (k+2)) => τ 0 = c ∧ τ 1 = d)).card

theorem exists_perm_zero_one (c d : Fin (k+2)) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm (Fin (k+2)), g 0 = c ∧ g 1 = d := by
  let g1 : Equiv.Perm (Fin (k+2)) := Equiv.swap 0 c
  have h10 : g1 0 = c := Equiv.swap_apply_left 0 c
  have hc1 : c ≠ g1 1 := by
    rw [← h10]; exact fun e => fin_zero_ne_one' (g1.injective e)
  refine ⟨Equiv.swap (g1 1) d * g1, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, h10, Equiv.swap_apply_of_ne_of_ne hc1 hcd]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem F_eq (c d : Fin (k+2)) (hcd : c ≠ d) : F c d = F (k := k) 0 1 := by
  obtain ⟨g, hg0, hg1⟩ := exists_perm_zero_one c d hcd
  unfold F
  symm
  refine Finset.card_nbij' (fun τ => g * τ) (fun τ => g⁻¹ * τ) ?_ ?_ ?_ ?_
  · intro τ hτ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    simp [Equiv.Perm.mul_apply, hτ.1, hτ.2, hg0, hg1]
  · intro τ hτ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ.1, hτ.2, Equiv.Perm.inv_eq_iff_eq,
      Equiv.Perm.inv_eq_iff_eq]
    exact ⟨hg0.symm, hg1.symm⟩
  · intro τ _; simp
  · intro τ _; simp

theorem F_diag (c : Fin (k+2)) : F c c = 0 := by
  unfold F
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro τ - ⟨h0, h1⟩
  exact fin_zero_ne_one' (τ.injective (h0.trans h1.symm))

theorem F_mul : F (k := k) 0 1 * ((k+2) * (k+1)) = (k+2).factorial := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Equiv.Perm (Fin (k+2)))))
    (t := (Finset.univ : Finset (Fin (k+2) × Fin (k+2))))
    (f := fun τ => (τ 0, τ 1)) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
  rw [h, Fintype.sum_prod_type]
  have hrow : ∀ c : Fin (k+2),
      ∑ d : Fin (k+2), (Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (k+2)) => (τ 0, τ 1) = (c, d))).card = (k+1) * F (k := k) 0 1 := by
    intro c
    have hfd : ∀ d, (Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (k+2)) => (τ 0, τ 1) = (c, d))).card = F c d := by
      intro d; unfold F; simp only [Prod.mk.injEq]
    simp only [hfd]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), F_diag, zero_add]
    rw [Finset.sum_congr rfl (fun d hd => F_eq c d (Ne.symm (Finset.ne_of_mem_erase hd)))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    simp
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- Worker rankings with prescribed orders at two distinct workers. -/
theorem card_workers (a b : Fin (k+2)) (hab : a ≠ b) :
    (Finset.univ.filter (fun W : Fin (k+2) → Equiv.Perm (Fin 2) =>
      W a 1 < W a 0 ∧ ¬ (W b 1 < W b 0))).card = 2 ^ k := by
  classical
  let T : Fin (k+2) → Finset (Equiv.Perm (Fin 2)) := fun i =>
    if i = a then Finset.univ.filter (fun s => s 1 < s 0)
    else if i = b then Finset.univ.filter (fun s => ¬ (s 1 < s 0)) else Finset.univ
  have hset : (Finset.univ.filter (fun W : Fin (k+2) → Equiv.Perm (Fin 2) =>
      W a 1 < W a 0 ∧ ¬ (W b 1 < W b 0))) = Fintype.piFinset T := by
    ext W
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, T]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hia : i = a
      · subst hia; simpa using h1
      · by_cases hib : i = b
        · subst hib; simpa [hia] using h2
        · simp [hia, hib]
    · intro h
      have h1 := h a
      have h2 := h b
      simp [Ne.symm hab] at h1 h2
      exact ⟨h1, not_lt.mpr h2⟩
  have c1 : (Finset.univ.filter (fun s : Equiv.Perm (Fin 2) => s 1 < s 0)).card = 1 := by decide
  have c2 : (Finset.univ.filter (fun s : Equiv.Perm (Fin 2) => ¬ (s 1 < s 0))).card = 1 := by
    decide
  have c3 : (Finset.univ : Finset (Equiv.Perm (Fin 2))).card = 2 := by decide
  rw [hset, Fintype.card_piFinset]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]
  have hrest : ∀ i ∈ (Finset.univ.erase a).erase b, (T i).card = 2 := by
    intro i hi
    have hib := Finset.ne_of_mem_erase hi
    have hia := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    simp [T, hia, hib, c3]
  rw [Finset.prod_congr rfl hrest, Finset.prod_const]
  have hcard : ((Finset.univ.erase a).erase b).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  simp [T, Ne.symm hab, c1, hcard]
  decide


/-- Profiles with two firms as pairs of firm rankings and a family of worker rankings. -/
def profEquiv (m : ℕ) :
    Profile 2 m ≃ (Equiv.Perm (Fin m) × Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin 2)) where
  toFun p := ((p.firmRank 0, p.firmRank 1), p.workerRank)
  invFun x := ⟨![x.1.1, x.1.2], x.2⟩
  left_inv p := by
    cases p with
    | mk fr wr =>
      simp only [Profile.mk.injEq, and_true]
      funext i; fin_cases i <;> rfl
  right_inv := fun _ => rfl

theorem profEquiv_symm_apply (m : ℕ) (x : (Equiv.Perm (Fin m) × Equiv.Perm (Fin m)) × (Fin m → Equiv.Perm (Fin 2))) :
    (profEquiv m).symm x = ⟨![x.1.1, x.1.2], x.2⟩ := rfl

theorem card_firms (c d : Fin (k+2)) (hcd : c ≠ d) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k+2)) => d = σ.symm 1 ∧ σ.symm 0 = c)).card =
      F (k := k) 0 1 := by
  rw [← F_eq c d hcd]
  unfold F
  refine Finset.card_nbij' (fun σ => σ⁻¹) (fun σ => σ⁻¹) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    rw [Equiv.Perm.inv_def]; exact ⟨hσ.2, hσ.1.symm⟩
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp only [Equiv.Perm.inv_def] at hσ ⊢
    simp only [Equiv.symm_symm]
    exact ⟨hσ.2.symm, hσ.1⟩
  · intro σ _; simp
  · intro σ _; simp

theorem card_C : (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card =
    (k+2).factorial * (F (k := k) 0 1 * 2 ^ k) := by
  rw [Finset.card_filter, ← (profEquiv (k+2)).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  have inner : ∀ σA σB : Equiv.Perm (Fin (k+2)),
      (∑ W, if C ((profEquiv (k+2)).symm ((σA, σB), W)) then 1 else 0) =
        if (σA.symm 0 = σB.symm 1 ∧ σB.symm 0 = σA.symm 1) then 2 ^ k else 0 := by
    intro σA σB
    have hC : ∀ W, C ((profEquiv (k+2)).symm ((σA, σB), W)) ↔
        (σA.symm 0 = σB.symm 1 ∧ σB.symm 0 = σA.symm 1 ∧ W (σA.symm 0) 1 < W (σA.symm 0) 0 ∧
          ¬ W (σB.symm 0) 1 < W (σB.symm 0) 0) := fun W => Iff.rfl
    split_ifs with h
    · have hne : σA.symm 0 ≠ σA.symm 1 := fun e => fin_zero_ne_one' (σA.symm.injective e)
      rw [← card_workers (σA.symm 0) (σA.symm 1) hne, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro W _
      apply if_congr _ rfl rfl
      rw [hC W]
      constructor
      · rintro ⟨-, -, h3, h4⟩; exact ⟨h3, by rwa [h.2] at h4⟩
      · rintro ⟨h3, h4⟩; exact ⟨h.1, h.2, h3, by rwa [h.2]⟩
    · apply Finset.sum_eq_zero
      intro W _
      rw [if_neg]
      rw [hC W]
      rintro ⟨h1, h2, -⟩
      exact h ⟨h1, h2⟩
  simp only [inner]
  have outer : ∀ σA : Equiv.Perm (Fin (k+2)),
      (∑ σB : Equiv.Perm (Fin (k+2)),
        if (σA.symm 0 = σB.symm 1 ∧ σB.symm 0 = σA.symm 1) then 2 ^ k else 0) =
        F (k := k) 0 1 * 2 ^ k := by
    intro σA
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have hne : σA.symm 1 ≠ σA.symm 0 := fun e => fin_zero_ne_one' (σA.symm.injective e).symm
    exact card_firms (σA.symm 1) (σA.symm 0) hne
  simp only [outer, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    smul_eq_mul]

theorem card_C_mul : (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card *
    (4 * ((k+2) * (k+1))) = Fintype.card (Profile 2 (k+2)) := by
  rw [card_C, card_profile]
  have h := F_mul (k := k)
  calc (k+2).factorial * (F (k := k) 0 1 * 2 ^ k) * (4 * ((k+2) * (k+1)))
      = (k+2).factorial * 2 ^ k * 4 * (F (k := k) 0 1 * ((k+2) * (k+1))) := by ring
    _ = (k+2).factorial ^ 2 * (Nat.factorial 2) ^ (k+2) := by
        rw [h, Nat.factorial_two]; ring

theorem sum_countB : (∑ p : Profile 2 (k+2), countB p) =
    Fintype.card (Profile 2 (k+2)) + (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card := by
  simp only [countB_two]
  rw [Finset.card_filter, ← Finset.card_univ, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> rfl

theorem sum_countB_sq : (∑ p : Profile 2 (k+2), countB p ^ 2) =
    Fintype.card (Profile 2 (k+2)) +
      3 * (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card := by
  simp only [countB_two]
  rw [Finset.card_filter, ← Finset.card_univ, Finset.card_eq_sum_ones, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> rfl

end

/-- Two firms, `m ≥ 2` workers: `E[S] = 1 + 1/(4m(m-1))`. -/
theorem expected_two (m : ℕ) (hm : 2 ≤ m) :
    expectedNumStableMatchings 2 m = 1 + 1 / (4 * (m : ℝ) * ((m : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [expected_eq_sum, sum_countB, ← card_C_mul]
  have hc : 0 < (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card := by
    rw [card_C]
    have := F_mul (k := k)
    have hF : 0 < F (k := k) 0 1 := by
      rcases Nat.eq_zero_or_pos (F (k := k) 0 1) with h0 | h0
      · rw [h0, zero_mul] at this; exact absurd this.symm (Nat.factorial_ne_zero _)
      · exact h0
    positivity
  generalize (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card = c at *
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  push_cast
  rw [show ((k:ℝ) + 2 - 1) = (k:ℝ) + 1 by ring]
  field_simp

/-- Two firms, `m ≥ 2` workers: `E[S^2] = 1 + 3/(4m(m-1))`. -/
theorem secondMoment_two (m : ℕ) (hm : 2 ≤ m) :
    secondMomentNumStableMatchings 2 m = 1 + 3 / (4 * (m : ℝ) * ((m : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [secondMoment_eq_sum, sum_countB_sq, ← card_C_mul]
  have hc : 0 < (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card := by
    rw [card_C]
    have := F_mul (k := k)
    have hF : 0 < F (k := k) 0 1 := by
      rcases Nat.eq_zero_or_pos (F (k := k) 0 1) with h0 | h0
      · rw [h0, zero_mul] at this; exact absurd this.symm (Nat.factorial_ne_zero _)
      · exact h0
    positivity
  generalize (Finset.univ.filter (fun p : Profile 2 (k+2) => C p)).card = c at *
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  push_cast
  rw [show ((k:ℝ) + 2 - 1) = (k:ℝ) + 1 by ring]
  field_simp

end PittelNTwo
