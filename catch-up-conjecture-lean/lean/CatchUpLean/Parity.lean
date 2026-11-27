import FormalConjectures.Paper.CatchUpConjecture

/-! Parity lemma for Catch-Up: a drawn position has even total; hence for odd `T_N`
the game on `{1,...,N}` is never a draw (complement of the conjecture's parity condition). -/

namespace CatchUpOMA
open CatchUp

theorem best_eq' (os : List Outcome) : Outcome.best os =
    if Outcome.win ∈ os then .win else if Outcome.draw ∈ os then .draw else .loss := by
  unfold Outcome.best
  induction os using List.reverseRecOn with
  | nil => simp
  | append_singleton l o ih =>
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, List.mem_append, List.mem_singleton]
    by_cases hw : Outcome.win ∈ l <;> by_cases hd : Outcome.draw ∈ l <;> cases o <;> simp [hw, hd]

theorem draw_mem_of_best {os : List Outcome} (h : Outcome.best os = .draw) :
    Outcome.draw ∈ os := by
  rw [best_eq'] at h; split_ifs at h with h1 h2 <;> simp_all

theorem neg_eq_draw {o : Outcome} (h : o.neg = .draw) : o = .draw := by
  cases o <;> simp_all [Outcome.neg]

theorem valueAux_empty_draw {a b : ℕ} {f : Bool} (h : valueAux ∅ a b f = .draw) :
    Even (a + b + ∑ x ∈ (∅ : Finset ℕ), x) := by
  rw [valueAux] at h
  simp only [if_true] at h
  split_ifs at h with h1 h2
  have hab : a = b := by omega
  subst hab
  exact ⟨a, by simp⟩

theorem valueAux_draw_even (n : ℕ) : ∀ (R : Finset ℕ) (a b : ℕ) (f : Bool), R.card ≤ n →
    valueAux R a b f = .draw → Even (a + b + ∑ x ∈ R, x) := by
  induction n with
  | zero =>
    intro R a b f hc h
    have : R = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    exact valueAux_empty_draw h
  | succ n ih =>
    intro R a b f hc h
    by_cases h0 : R = ∅
    · subst h0; exact valueAux_empty_draw h
    rw [valueAux] at h
    simp only [h0, if_false] at h
    by_cases hlt : a + ∑ x ∈ R, x < b
    · simp [hlt] at h
    rw [if_neg hlt] at h
    have hm := draw_mem_of_best h
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and,
      Subtype.exists] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hs : ∑ y ∈ R.erase x, y + x = ∑ y ∈ R, y := Finset.sum_erase_add _ _ hx
    have hcard : (R.erase x).card ≤ n := by
      rw [Finset.card_erase_of_mem hx]; omega
    split_ifs at hxe
    · have := ih _ _ _ _ hcard (neg_eq_draw hxe)
      have e : a + b + ∑ y ∈ R, y = b + (a + x) + ∑ y ∈ R.erase x, y := by omega
      rw [e]; exact this
    · have := ih _ _ _ _ hcard (neg_eq_draw hxe)
      have e : a + b + ∑ y ∈ R, y = b + (a + x) + ∑ y ∈ R.erase x, y := by omega
      rw [e]; exact this
    · have := ih _ _ _ _ hcard hxe
      have e : a + b + ∑ y ∈ R, y = (a + x) + b + ∑ y ∈ R.erase x, y := by omega
      rw [e]; exact this

theorem sum_Icc_id_two (N : ℕ) : 2 * ∑ x ∈ Finset.Icc 1 N, x = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring

theorem sum_Icc_id (N : ℕ) : ∑ x ∈ Finset.Icc 1 N, x = N * (N + 1) / 2 := by
  have := sum_Icc_id_two N; omega

/-- If `T_N` is odd, Catch-Up on `{1,...,N}` is not a draw. -/
theorem value_ne_draw_of_odd (N : ℕ) (h : ¬ Even (N * (N + 1) / 2)) :
    value (Finset.Icc 1 N) ≠ .draw := by
  intro hv
  have := valueAux_draw_even _ _ 0 0 true le_rfl hv
  rw [zero_add, zero_add, sum_Icc_id] at this
  exact h this

/-- Hence the conjecture is equivalent to: for every `N`, `value (Icc 1 N) = draw` iff `T_N` is even. -/
theorem conj_iff (h : ∀ N : ℕ, Even (N * (N + 1) / 2) → value (.Icc 1 N) = .draw) (N : ℕ) :
    value (.Icc 1 N) = .draw ↔ Even (N * (N + 1) / 2) := by
  constructor
  · intro hv; by_contra hn; exact value_ne_draw_of_odd N hn hv
  · exact h N

end CatchUpOMA
