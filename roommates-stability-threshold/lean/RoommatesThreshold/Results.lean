import FormalConjectures.Paper.ApproximatelyStableMatching

/-!
# Kernel-checked results on `Roommates.stabilityThreshold`
(self-contained; all proofs by elementary tactics and `decide`, no `native_decide`)

* `stabilityThreshold_le_half` : `K(n) ≤ ⌈n/2⌉` for `n ≥ 1` (upper half of the conjecture).
* `stabilityThreshold_mono`    : `K(n) ≤ K(n+1)`.
* `K3, K4, K5, K6`             : `K(3)=2, K(4)=2, K(5)=3, K(6)=3`.
* `three_le_K`                 : `3 ≤ K(N)` for all `N ≥ 5`.
* `target_of_lowerBound`       : the target follows from the lower-bound hypothesis.
-/

namespace RoommatesThreshold

open Roommates

variable {n : ℕ}

/- ## Upper bound -/

/-- Every matched agent ranks its partner within its top `t`. -/
def Valid (p : CompleteProfile n) (t : ℕ) (μ : Matching (Fin n)) : Prop :=
  ∀ i, μ.val i = i ∨ p.partnerRank i (μ.val i) ≤ t

/-- Number of matched agents. -/
def numMatched (μ : Matching (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i => μ.val i ≠ i)).card

/-- Match two single agents `i ≠ j` to each other. -/
def addPair (μ : Matching (Fin n)) (i j : Fin n) (hi : μ.val i = i) (hj : μ.val j = j)
    (hij : i ≠ j) : Matching (Fin n) := by
  classical
  let f : Fin n → Fin n := fun x => if x = i then j else if x = j then i else μ.val x
  have hf : Function.Involutive f := by
    intro x
    by_cases hxi : x = i
    · subst hxi; simp [f, Ne.symm hij]
    · by_cases hxj : x = j
      · subst hxj; simp [f]
      · have h1 : μ.val x ≠ i := by
          intro h; apply hxi; apply μ.val.injective; rw [h, hi]
        have h2 : μ.val x ≠ j := by
          intro h; apply hxj; apply μ.val.injective; rw [h, hj]
        simp [f, hxi, hxj, h1, h2, μ.2 x]
  exact ⟨Function.Involutive.toPerm f hf, hf⟩

theorem addPair_apply (μ : Matching (Fin n)) (i j : Fin n) (hi : μ.val i = i) (hj : μ.val j = j)
    (hij : i ≠ j) (x : Fin n) :
    (addPair μ i j hi hj hij).val x = if x = i then j else if x = j then i else μ.val x := by
  classical
  rfl

theorem exists_valid_max (p : CompleteProfile n) (t : ℕ) :
    ∃ μ : Matching (Fin n), Valid p t μ ∧
      ∀ ν : Matching (Fin n), Valid p t ν → numMatched ν ≤ numMatched μ := by
  classical
  let S : Finset (Matching (Fin n)) := Finset.univ.filter (fun μ => Valid p t μ)
  have hS : S.Nonempty :=
    ⟨emptyMatching _, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun _ => Or.inl rfl⟩⟩
  obtain ⟨μ, hμS, hμ⟩ := Finset.exists_max_image S numMatched hS
  refine ⟨μ, (Finset.mem_filter.1 hμS).2, fun ν hν => hμ ν ?_⟩
  simp [S, hν]

theorem numMatched_addPair_lt (μ : Matching (Fin n)) (i j : Fin n) (hi : μ.val i = i)
    (hj : μ.val j = j) (hij : i ≠ j) : numMatched μ < numMatched (addPair μ i j hi hj hij) := by
  classical
  unfold numMatched
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, ?_, ?_⟩
    · simp [addPair_apply, Ne.symm hij]
    · simp [hi]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [addPair_apply]
    by_cases hxi : x = i
    · rw [if_pos hxi, hxi]; exact Ne.symm hij
    · by_cases hxj : x = j
      · rw [if_neg hxi, if_pos hxj, hxj]; exact hij
      · rw [if_neg hxi, if_neg hxj]; exact hx

theorem partnerRank_pos (p : CompleteProfile n) (i j : Fin n) : 1 ≤ p.partnerRank i j := by
  unfold CompleteProfile.partnerRank; omega

/-- Every complete profile has a `⌈n/2⌉`-stable matching. -/
theorem exists_kStable_half (p : CompleteProfile n) :
    ∃ μ : Matching (Fin n), IsKStable ⊤ p.partnerRank ((n + 1) / 2) μ := by
  classical
  set k := (n + 1) / 2 with hk
  obtain ⟨μ, hval, hmax⟩ := exists_valid_max p (n - k)
  refine ⟨μ, ?_, ?_⟩
  · intro i
    by_cases h : μ.val i = i
    · exact Or.inl h
    · exact Or.inr ((SimpleGraph.top_adj _ _).2 (Ne.symm h))
  · rintro i j ⟨hadj, hne, hi, hj⟩
    have hij : i ≠ j := (SimpleGraph.top_adj _ _).1 hadj
    have pi := partnerRank_pos p i j
    have pj := partnerRank_pos p j i
    have hsi : μ.val i = i := by
      rcases hval i with h | h
      · exact h
      · exfalso; omega
    have hsj : μ.val j = j := by
      rcases hval j with h | h
      · exact h
      · exfalso; omega
    rw [hsi, p.partnerRank_self] at hi
    rw [hsj, p.partnerRank_self] at hj
    have hv : Valid p (n - k) (addPair μ i j hsi hsj hij) := by
      intro x
      rw [addPair_apply]
      by_cases hxi : x = i
      · right; rw [if_pos hxi, hxi]; omega
      · by_cases hxj : x = j
        · right; rw [if_neg hxi, if_pos hxj, hxj]; omega
        · rw [if_neg hxi, if_neg hxj]; exact hval x
    have h1 := hmax _ hv
    have h2 := numMatched_addPair_lt μ i j hsi hsj hij
    omega

/-- **Upper bound:** `K(n) ≤ ⌈n/2⌉` for `n ≥ 1`. -/
theorem stabilityThreshold_le_half (hn : 0 < n) : stabilityThreshold n ≤ (n + 1) / 2 :=
  stabilityThreshold_le (by omega) exists_kStable_half

/- ## Lower bounds from explicit profiles -/

theorem isKStable_mono {α : Type*} {G : SimpleGraph α} {r : α → α → ℕ} {k l : ℕ}
    {μ : Matching α} (h : IsKStable G r k μ) (hkl : k ≤ l) : IsKStable G r l μ := by
  refine ⟨h.1, fun i j hb => h.2 i j ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hb
  exact ⟨h1, h2, by omega, by omega⟩

/-- A profile with no `k`-stable matching forces `K(n) > k`. -/
theorem lt_stabilityThreshold {k : ℕ} (p : CompleteProfile n)
    (hp : ∀ μ : Matching (Fin n), ¬ IsKStable ⊤ p.partnerRank k μ) :
    k < stabilityThreshold n := by
  by_contra hcon
  obtain ⟨-, hspec⟩ := stabilityThreshold_spec n
  obtain ⟨μ, hμ⟩ := hspec p
  exact hp μ (isKStable_mono hμ (by omega))

/-- Four agents, no stable matching (k = 1). Rank vectors are zero-based, own name last. -/
noncomputable def four : CompleteProfile 4 where
  rank := ![Equiv.ofBijective ![3, 0, 1, 2] (by decide),
    Equiv.ofBijective ![2, 3, 0, 1] (by decide),
    Equiv.ofBijective ![2, 1, 3, 0] (by decide),
    Equiv.ofBijective ![2, 0, 1, 3] (by decide)]
  self_last := by decide

theorem four_no_stable : ∀ μ : Matching (Fin 4), ¬ IsKStable ⊤ four.partnerRank 1 μ := by
  unfold IsKStable IsAcceptable IsKBlockingPair
  decide

/-- Five agents, no 2-stable matching. -/
noncomputable def five : CompleteProfile 5 where
  rank := ![Equiv.ofBijective ![4, 0, 1, 2, 3] (by decide),
    Equiv.ofBijective ![0, 4, 2, 1, 3] (by decide),
    Equiv.ofBijective ![3, 1, 4, 0, 2] (by decide),
    Equiv.ofBijective ![1, 3, 2, 4, 0] (by decide),
    Equiv.ofBijective ![3, 1, 0, 2, 4] (by decide)]
  self_last := by decide

theorem five_no_two_stable : ∀ μ : Matching (Fin 5), ¬ IsKStable ⊤ five.partnerRank 2 μ := by
  unfold IsKStable IsAcceptable IsKBlockingPair
  decide

/- ## Monotonicity by padding with a dummy agent -/


/-- Zero-based ranks of the padded profile. -/
def padFun (p : CompleteProfile n) (i x : Fin (n + 1)) : Fin (n + 1) :=
  if hi : i = Fin.last n then x
  else if hx : x = Fin.last n then (p.rank (i.castPred hi) (i.castPred hi)).castSucc
  else if x = i then Fin.last n
  else (p.rank (i.castPred hi) (x.castPred hx)).castSucc

theorem padFun_last (p : CompleteProfile n) (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    padFun p i (Fin.last n) = (p.rank (i.castPred hi) (i.castPred hi)).castSucc := by
  simp [padFun, hi]

theorem padFun_self (p : CompleteProfile n) (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    padFun p i i = Fin.last n := by
  simp [padFun, hi]

theorem padFun_other (p : CompleteProfile n) (i x : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (hx : x ≠ Fin.last n) (hxi : x ≠ i) :
    padFun p i x = (p.rank (i.castPred hi) (x.castPred hx)).castSucc := by
  simp [padFun, hi, hx, hxi]

theorem padFun_injective (p : CompleteProfile n) (i : Fin (n + 1)) :
    Function.Injective (padFun p i) := by
  intro x y h
  by_cases hi : i = Fin.last n
  · simpa [padFun, hi] using h
  · have cls : ∀ z : Fin (n + 1), z = Fin.last n ∨ z = i ∨ (z ≠ Fin.last n ∧ z ≠ i) := by
      intro z
      by_cases h1 : z = Fin.last n
      · exact Or.inl h1
      · by_cases h2 : z = i
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
    rcases cls x with hx | hx | ⟨hx1, hx2⟩ <;> rcases cls y with hy | hy | ⟨hy1, hy2⟩
    · rw [hx, hy]
    · rw [hx, hy, padFun_last p i hi, padFun_self p i hi] at h
      exact absurd h (Fin.castSucc_ne_last _)
    · rw [hx, padFun_last p i hi, padFun_other p i y hi hy1 hy2] at h
      have h' := congrArg Fin.castSucc ((p.rank _).injective (Fin.castSucc_injective _ h))
      rw [Fin.castSucc_castPred, Fin.castSucc_castPred] at h'
      exact absurd h'.symm hy2
    · rw [hx, hy, padFun_last p i hi, padFun_self p i hi] at h
      exact absurd h.symm (Fin.castSucc_ne_last _)
    · rw [hx, hy]
    · rw [hx, padFun_self p i hi, padFun_other p i y hi hy1 hy2] at h
      exact absurd h.symm (Fin.castSucc_ne_last _)
    · rw [hy, padFun_last p i hi, padFun_other p i x hi hx1 hx2] at h
      have h' := congrArg Fin.castSucc ((p.rank _).injective (Fin.castSucc_injective _ h))
      rw [Fin.castSucc_castPred, Fin.castSucc_castPred] at h'
      exact absurd h' hx2
    · rw [hy, padFun_self p i hi, padFun_other p i x hi hx1 hx2] at h
      exact absurd h (Fin.castSucc_ne_last _)
    · rw [padFun_other p i x hi hx1 hx2, padFun_other p i y hi hy1 hy2] at h
      have h' := (p.rank _).injective (Fin.castSucc_injective _ h)
      have h'' := congrArg Fin.castSucc h'
      rwa [Fin.castSucc_castPred, Fin.castSucc_castPred] at h''

/-- The padded profile. -/
noncomputable def pad (p : CompleteProfile n) : CompleteProfile (n + 1) where
  rank i := Equiv.ofBijective (padFun p i) (Finite.injective_iff_bijective.mp (padFun_injective p i))
  self_last i := by
    simp only [Equiv.ofBijective_apply]
    unfold padFun
    by_cases hi : i = Fin.last n
    · simp [hi]
    · simp [hi]

theorem pad_rank_castSucc (p : CompleteProfile n) (a b : Fin n) (hab : b ≠ a) :
    (pad p).partnerRank a.castSucc b.castSucc = p.partnerRank a b := by
  simp [pad, CompleteProfile.partnerRank, padFun, Fin.castSucc_ne_last, hab]

theorem pad_rank_last (p : CompleteProfile n) (a : Fin n) :
    (pad p).partnerRank a.castSucc (Fin.last n) = p.partnerRank a a := by
  simp [pad, CompleteProfile.partnerRank, padFun, Fin.castSucc_ne_last]

/-- Restriction of a matching of the padded market. -/
def restrictFun (μ : Matching (Fin (n + 1))) (a : Fin n) : Fin n :=
  if h : μ.val a.castSucc = Fin.last n then a else (μ.val a.castSucc).castPred h

theorem restrictFun_involutive (μ : Matching (Fin (n + 1))) :
    Function.Involutive (restrictFun μ) := by
  intro a
  by_cases h : μ.val a.castSucc = Fin.last n
  · have e : restrictFun μ a = a := by simp [restrictFun, h]
    rw [e, e]
  · have e : restrictFun μ a = (μ.val a.castSucc).castPred h := by simp [restrictFun, h]
    have hb : μ.val ((μ.val a.castSucc).castPred h).castSucc = a.castSucc := by
      rw [Fin.castSucc_castPred, μ.2]
    have hb' : μ.val ((μ.val a.castSucc).castPred h).castSucc ≠ Fin.last n := by
      rw [hb]; exact Fin.castSucc_ne_last a
    rw [e]
    have e2 : restrictFun μ ((μ.val a.castSucc).castPred h)
        = (μ.val ((μ.val a.castSucc).castPred h).castSucc).castPred hb' := by
      simp only [restrictFun, dif_neg hb']
    rw [e2]
    apply Fin.castSucc_injective
    rw [Fin.castSucc_castPred, hb]

def restrict (μ : Matching (Fin (n + 1))) : Matching (Fin n) :=
  ⟨Function.Involutive.toPerm _ (restrictFun_involutive μ), restrictFun_involutive μ⟩

theorem restrict_apply (μ : Matching (Fin (n + 1))) (a : Fin n) :
    (restrict μ).val a = restrictFun μ a := rfl

/-- Ranks only go up when passing to the padded market. -/
theorem rank_le_pad (p : CompleteProfile n) (μ : Matching (Fin (n + 1))) (a : Fin n) :
    p.partnerRank a ((restrict μ).val a) ≤ (pad p).partnerRank a.castSucc (μ.val a.castSucc) := by
  rw [restrict_apply]
  unfold restrictFun
  by_cases h : μ.val a.castSucc = Fin.last n
  · simp only [h, dite_true]; rw [pad_rank_last]
  · simp only [h, dite_false]
    by_cases h2 : μ.val a.castSucc = a.castSucc
    · have h3 : (μ.val a.castSucc).castPred h = a := by simp [h2]
      rw [h3, h2, (pad p).partnerRank_self, p.partnerRank_self]; omega
    · have hb : (μ.val a.castSucc).castPred h ≠ a := by
        intro hc; apply h2
        have hc' := congrArg Fin.castSucc hc
        rw [Fin.castSucc_castPred] at hc'
        exact hc'
      have := pad_rank_castSucc p a _ hb
      rw [Fin.castSucc_castPred] at this
      rw [this]

theorem restrict_ne (μ : Matching (Fin (n + 1))) (a b : Fin n)
    (h : (restrict μ).val a ≠ b) : μ.val a.castSucc ≠ b.castSucc := by
  intro hc; apply h
  rw [restrict_apply]; unfold restrictFun
  have : μ.val a.castSucc ≠ Fin.last n := by rw [hc]; exact Fin.castSucc_ne_last b
  simp [this, hc]

/-- **Monotonicity of the threshold.** -/
theorem stabilityThreshold_mono (n : ℕ) : stabilityThreshold n ≤ stabilityThreshold (n + 1) := by
  obtain ⟨hpos, hspec⟩ := stabilityThreshold_spec (n + 1)
  apply stabilityThreshold_le hpos
  intro p
  obtain ⟨μ', -, hμ'⟩ := hspec (pad p)
  refine ⟨restrict μ', fun i => ?_, ?_⟩
  · by_cases h : (restrict μ').val i = i
    · exact Or.inl h
    · exact Or.inr ((SimpleGraph.top_adj _ _).2 (Ne.symm h))
  · rintro a b ⟨hadj, hne, ha, hb⟩
    have hab : a ≠ b := (SimpleGraph.top_adj _ _).1 hadj
    apply hμ' a.castSucc b.castSucc
    refine ⟨(SimpleGraph.top_adj _ _).2 (fun h => hab (Fin.castSucc_injective _ h)),
      restrict_ne μ' a b hne, ?_, ?_⟩
    · rw [pad_rank_castSucc p a b (Ne.symm hab)]
      exact le_trans ha (rank_le_pad p μ' a)
    · rw [pad_rank_castSucc p b a hab]
      have hne' : (restrict μ').val b ≠ a := by
        intro h; apply hne; rw [← h, (restrict μ').2 b]
      exact le_trans hb (rank_le_pad p μ' b)


/- ## Exact small values and the general lower bound -/

theorem K3 : stabilityThreshold 3 = 2 := by
  have h1 := stabilityThreshold_le_half (n := 3) (by norm_num)
  have h2 : 1 < stabilityThreshold 3 := lt_stabilityThreshold CompleteProfile.cyclicThree
    (fun μ h => CompleteProfile.not_isStable_cyclicThree μ ((isKStable_one _ _ _).1 h))
  omega

theorem K4 : stabilityThreshold 4 = 2 := by
  have h1 := stabilityThreshold_le_half (n := 4) (by norm_num)
  have h2 := lt_stabilityThreshold four four_no_stable
  omega

theorem K5 : stabilityThreshold 5 = 3 := by
  have h1 := stabilityThreshold_le_half (n := 5) (by norm_num)
  have h2 := lt_stabilityThreshold five five_no_two_stable
  omega

theorem K6 : stabilityThreshold 6 = 3 := by
  have h1 := stabilityThreshold_le_half (n := 6) (by norm_num)
  have h2 : stabilityThreshold 5 ≤ stabilityThreshold 6 := stabilityThreshold_mono 5
  rw [K5] at h2
  omega

theorem three_le_K : ∀ N ≥ 5, 3 ≤ stabilityThreshold N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [K5]
  | succ N _ ih => exact le_trans ih (stabilityThreshold_mono N)

/-- **L3 reduction.** The target follows from the (named) lower-bound hypothesis
`∃ N₀ ≥ 3, ∀ N ≥ N₀, ⌈N/2⌉ ≤ K(N)`, since the upper bound is proved above.
(Computationally the hypothesis already fails at `N = 7`: `K(7) = 3 < 4`.) -/
theorem target_of_lowerBound
    (h : ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, (N + 1) / 2 ≤ stabilityThreshold N) :
    type_of% @FanelliMoscardelli.stability_threshold_tight := by
  obtain ⟨N₀, h3, hN⟩ := h
  refine ⟨N₀, h3, fun N hN' => ?_⟩
  have := stabilityThreshold_le_half (n := N) (by omega)
  have := hN N hN'
  omega

end RoommatesThreshold
