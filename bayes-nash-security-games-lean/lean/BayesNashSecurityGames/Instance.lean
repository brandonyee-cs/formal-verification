import FormalConjectures.Arxiv.«2610.08796».BayesianSecurityGames

/-!
# A concrete two-type instance (L2 evidence)

Game: 2 targets, 1 resource, defender payoffs `(-3, 2)` and `(-5, 0)`,
two equally likely attacker types with payoffs `[(0,-4), (4,-4)]` and `[(4,-1), (0,-3)]`.
Equilibrium (found by `scripts/bne_enum.py`): coverage `(1/3, 2/3)`, type 1 attacks target 1,
type 2 attacks target 0. Here defender coverage is not unique: every `c₀ ∈ [1/3, 7/8]` works
with the same attacks (`instance_isBayesNash_family`).
-/

open Arxiv.«2610.08796»

namespace OMA.BNSG

def g₀ : GameInput :=
  (1, [(-3, 2), (-5, 0)], [(1/2, [(0, -4), (4, -4)]), (1/2, [(4, -1), (0, -3)])])

theorem sumT (f : Fin g₀.numTargets → ℚ) : ∑ t, f t = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ :=
  Fin.sum_univ_two f

theorem sumΘ (f : Fin g₀.numTypes → ℚ) : ∑ t, f t = f ⟨0, by decide⟩ + f ⟨1, by decide⟩ :=
  Fin.sum_univ_two f

theorem forallT (p : Fin g₀.numTargets → Prop) : (∀ t, p t) ↔ p ⟨0, by decide⟩ ∧ p ⟨1, by decide⟩ :=
  Fin.forall_fin_two (p := p)

theorem forallΘ (p : Fin g₀.numTypes → Prop) : (∀ t, p t) ↔ p ⟨0, by decide⟩ ∧ p ⟨1, by decide⟩ :=
  Fin.forall_fin_two (p := p)

theorem g₀_valid : g₀.Valid := by
  unfold GameInput.Valid
  simp only [sumΘ, forallT, forallΘ]
  simp [g₀, GameInput.numTargets, GameInput.numTypes, GameInput.prior, GameInput.defenderPayoff,
    GameInput.attackerPayoffs, GameInput.attackerPayoff]
  norm_num

theorem instance_isBayesNash_family (x : ℚ) (h1 : 1/3 ≤ x) (h2 : x ≤ 7/8) :
    g₀.IsBayesNash ([x, 1 - x], [[0, 1], [1, 0]]) := by
  unfold GameInput.IsBayesNash
  dsimp only
  simp only [sumT, sumΘ, forallT, forallΘ]
  simp [g₀, GameInput.numTargets, GameInput.numTypes, GameInput.prior, GameInput.defenderPayoff,
    GameInput.attackerPayoffs, GameInput.attackerPayoff]
  refine ⟨⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    fun _ => by norm_num, fun _ => by norm_num⟩

theorem instance_isBayesNash : g₀.IsBayesNash ([1/3, 2/3], [[0, 1], [1, 0]]) := by
  have := instance_isBayesNash_family (1/3) le_rfl (by norm_num)
  norm_num at this ⊢
  exact this

end OMA.BNSG
