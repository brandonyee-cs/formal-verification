import FormalConjectures.Paper.CatchUpConjecture

namespace CatchUpOMA
open CatchUp

theorem best_eq (os : List Outcome) : Outcome.best os =
    if Outcome.win ∈ os then .win else if Outcome.draw ∈ os then .draw else .loss := by
  unfold Outcome.best
  induction os using List.reverseRecOn with
  | nil => simp
  | append_singleton l o ih =>
    rw [List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, List.mem_append, List.mem_singleton]
    by_cases hw : Outcome.win ∈ l <;> by_cases hd : Outcome.draw ∈ l <;> cases o <;> simp [hw, hd]

theorem best_congr {os os' : List Outcome} (h : ∀ o, o ∈ os ↔ o ∈ os') :
    Outcome.best os = Outcome.best os' := by
  simp only [best_eq, h]

/-- Final comparison. -/
def cmp (a b : ℕ) : Outcome := if a > b then .win else if b > a then .loss else .draw

/-- Computable, structurally recursive (on fuel) list version of `valueAux`. -/
def ev : ℕ → List ℕ → ℕ → ℕ → Bool → Outcome
  | 0, l, a, b, _ => if l = [] then cmp a b else .loss
  | n+1, l, a, b, f =>
    if l = [] then cmp a b else
    if a + l.sum < b then .loss else
    Outcome.best (l.map fun x =>
      if f then (ev n (l.erase x) b (a+x) false).neg
      else if a + x ≥ b then (ev n (l.erase x) b (a+x) false).neg
      else ev n (l.erase x) (a+x) b false)

theorem valueAux_eq_ev (n : ℕ) : ∀ (l : List ℕ) (a b : ℕ) (f : Bool),
    l.Nodup → l.length ≤ n → valueAux l.toFinset a b f = ev n l a b f := by
  induction n with
  | zero =>
    intro l a b f _ hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [valueAux]; simp [ev, cmp]
  | succ n ih =>
    intro l a b f hnd hl
    rw [valueAux]
    by_cases h0 : l = []
    · subst h0; simp [ev, cmp]
    · have hne : l.toFinset ≠ ∅ := by simpa [List.toFinset_eq_empty_iff] using h0
      have hsum : l.toFinset.sum (fun x => x) = l.sum := by
        rw [List.sum_toFinset _ hnd]; simp
      simp only [hne, if_false, ev, h0, hsum]
      by_cases hlt : a + l.sum < b
      · simp only [hlt, if_true]
      · rw [if_neg hlt, if_neg hlt]
        apply best_congr
        intro o
        have hx : ∀ x ∈ l, (l.toFinset.erase x) = (l.erase x).toFinset := by
          intro x _; ext y; simp [hnd.mem_erase_iff]
        have hlen : ∀ x ∈ l, (l.erase x).length ≤ n := by
          intro x hx; rw [List.length_erase_of_mem hx]; omega
        simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists,
          List.mem_toFinset]
        constructor
        · rintro ⟨x, hxl, rfl⟩
          refine ⟨x, hxl, ?_⟩
          simp only [hx x hxl, ih _ _ _ _ (hnd.erase x) (hlen x hxl)]
        · rintro ⟨x, hxl, rfl⟩
          refine ⟨x, hxl, ?_⟩
          simp only [hx x hxl, ih _ _ _ _ (hnd.erase x) (hlen x hxl)]

theorem best_eq_win (os : List Outcome) : Outcome.best os = .win ↔ Outcome.win ∈ os := by
  rw [best_eq]; split_ifs <;> simp_all

theorem best_ne_loss (os : List Outcome) :
    Outcome.best os ≠ .loss ↔ ∃ o ∈ os, o ≠ .loss := by
  rw [best_eq]
  constructor
  · intro h; split_ifs at h with h1 h2
    · exact ⟨_, h1, by simp⟩
    · exact ⟨_, h2, by simp⟩
    · exact absurd rfl h
  · rintro ⟨o, ho, hne⟩
    cases o
    · simp [ho]
    · exact absurd rfl hne
    · split_ifs <;> simp_all

theorem neg_eq_win (o : Outcome) : o.neg = .win ↔ o = .loss := by cases o <;> simp [Outcome.neg]
theorem neg_ne_loss (o : Outcome) : o.neg ≠ .loss ↔ o ≠ .win := by cases o <;> simp [Outcome.neg]

/-- Threshold (alpha-beta style) evaluator: `ge n true` tests `ev = win`, `ge n false` tests
`ev ≠ loss`.  Short-circuits through `List.any`. -/
def ge : ℕ → Bool → List ℕ → ℕ → ℕ → Bool → Bool
  | 0, w, l, a, b, _ => if l = [] then (if w then decide (b < a) else decide (b ≤ a)) else false
  | n+1, w, l, a, b, f =>
    if l = [] then (if w then decide (b < a) else decide (b ≤ a)) else
    if a + l.sum < b then false else
    l.any fun x =>
      if f || decide (b ≤ a + x) then !(ge n (!w) (l.erase x) b (a+x) false)
      else ge n w (l.erase x) (a+x) b false

theorem child_iff (n : ℕ)
    (ih : ∀ (w : Bool) (l : List ℕ) (a b : ℕ) (f : Bool),
      (ge n w l a b f = true) ↔ (if w then ev n l a b f = .win else ev n l a b f ≠ .loss))
    (w f : Bool) (l : List ℕ) (a b x : ℕ) :
    ((if f || decide (b ≤ a + x) then !(ge n (!w) (l.erase x) b (a+x) false)
      else ge n w (l.erase x) (a+x) b false) = true) ↔
    (if w then
      (if f then (ev n (l.erase x) b (a+x) false).neg
        else if a + x ≥ b then (ev n (l.erase x) b (a+x) false).neg
        else ev n (l.erase x) (a+x) b false) = .win
     else
      (if f then (ev n (l.erase x) b (a+x) false).neg
        else if a + x ≥ b then (ev n (l.erase x) b (a+x) false).neg
        else ev n (l.erase x) (a+x) b false) ≠ .loss) := by
  have hab := Nat.lt_or_ge (a + x) b
  cases w <;> cases f <;> rcases hab with hab | hab <;>
    simp [hab, Nat.not_le.mpr, ih, neg_ne_loss, neg_eq_win, Bool.eq_false_iff, -Bool.not_eq_true]

theorem ge_true_iff (n : ℕ) : ∀ (w : Bool) (l : List ℕ) (a b : ℕ) (f : Bool),
    (ge n w l a b f = true) ↔ (if w then ev n l a b f = .win else ev n l a b f ≠ .loss) := by
  induction n with
  | zero =>
    intro w l a b f
    by_cases h0 : l = []
    · subst h0; cases w <;> simp [ge, ev, cmp] <;> split_ifs <;> simp_all <;> omega
    · cases w <;> simp [ge, ev, h0]
  | succ n ih =>
    intro w l a b f
    by_cases h0 : l = []
    · subst h0; cases w <;> simp [ge, ev, cmp] <;> split_ifs <;> simp_all <;> omega
    · by_cases hlt : a + l.sum < b
      · cases w <;> simp [ge, ev, h0, hlt]
      · simp only [ge, ev, h0, hlt, if_false, List.any_eq_true, child_iff n ih]
        cases w
        · simp only [Bool.false_eq_true, if_false, best_ne_loss, List.mem_map]
          constructor
          · rintro ⟨x, hx, hb⟩
            exact ⟨_, ⟨x, hx, rfl⟩, hb⟩
          · rintro ⟨_, ⟨x, hx, rfl⟩, hb⟩
            exact ⟨x, hx, hb⟩
        · simp only [if_true, best_eq_win, List.mem_map]

theorem Icc_eq (N : ℕ) : Finset.Icc 1 N = (List.range' 1 N).toFinset := by
  ext y; simp only [Finset.mem_Icc, List.mem_toFinset, List.mem_range'_1]; omega

/-- Reduction of `value (Icc 1 N) = draw` to two Boolean kernel computations. -/
theorem value_eq_draw_of (N : ℕ)
    (h1 : ge N false (List.range' 1 N) 0 0 true = true)
    (h2 : ge N true (List.range' 1 N) 0 0 true = false) :
    value (Finset.Icc 1 N) = .draw := by
  have hv : value (Finset.Icc 1 N) = ev N (List.range' 1 N) 0 0 true := by
    rw [value, Icc_eq]; exact valueAux_eq_ev N _ _ _ _ List.nodup_range' (by simp)
  rw [ge_true_iff] at h1
  have h2' : ¬ (ge N true (List.range' 1 N) 0 0 true = true) := by simp [h2]
  rw [ge_true_iff] at h2'
  simp only [if_true, Bool.false_eq_true, if_false] at h1 h2'
  rw [hv]
  revert h1 h2'
  cases ev N (List.range' 1 N) 0 0 true <;> simp

theorem value_Icc_3 : value (Finset.Icc 1 3) = .draw :=
  value_eq_draw_of 3 (by decide +kernel) (by decide +kernel)
theorem value_Icc_4 : value (Finset.Icc 1 4) = .draw :=
  value_eq_draw_of 4 (by decide +kernel) (by decide +kernel)
theorem value_Icc_7 : value (Finset.Icc 1 7) = .draw :=
  value_eq_draw_of 7 (by decide +kernel) (by decide +kernel)
theorem value_Icc_8 : value (Finset.Icc 1 8) = .draw :=
  value_eq_draw_of 8 (by decide +kernel) (by decide +kernel)
theorem value_Icc_11 : value (Finset.Icc 1 11) = .draw :=
  value_eq_draw_of 11 (by decide +kernel) (by decide +kernel)
theorem value_Icc_12 : value (Finset.Icc 1 12) = .draw :=
  value_eq_draw_of 12 (by decide +kernel) (by decide +kernel)

/-- The conjecture holds for all `N ≤ 12`. -/
theorem conj_le_12 (N : ℕ) (hN : N ≤ 12) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw := by
  interval_cases N
  · exact value_eq_draw_of 0 (by decide +kernel) (by decide +kernel)
  all_goals first
    | exact value_Icc_3 | exact value_Icc_4 | exact value_Icc_7 | exact value_Icc_8
    | exact value_Icc_11 | exact value_Icc_12
    | (exfalso; revert h_even; decide)

end CatchUpOMA
