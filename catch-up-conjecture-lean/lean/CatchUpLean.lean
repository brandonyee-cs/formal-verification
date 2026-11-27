import CatchUpLean.Eval
import CatchUpLean.Parity
import CatchUpLean.Cert

/-!
# The Catch-Up conjecture: kernel-checked small cases and the parity lemma

Work on `CatchUp.value_of_even_mul_succ_self_div_two` (formal-conjectures,
`FormalConjectures/Paper/CatchUpConjecture.lean`), stated against the upstream definitions
`CatchUp.value` and `CatchUp.valueAux`.

* `CatchUpLean.Eval` (namespace `CatchUpOMA`): a computable list evaluator proved equal to
  `valueAux`, a threshold evaluator, and `conj_le_12`: the conjecture for every `N ≤ 12`, by
  `decide +kernel`.
* `CatchUpLean.Parity` (namespace `CatchUpOMA`): `value_ne_draw_of_odd`, for every `N`: if
  `N(N+1)/2` is odd, the game on `{1, ..., N}` is not a draw.
* `CatchUpLean.Cert` (namespace `CatchUpCert`): a certificate checker proved sound against
  `valueAux` (`check_sound`), generated certificates, and `conj_le_16`: the conjecture for every
  `N ≤ 16`.

The conjecture itself (all `N`) is open and is not proved here.
-/
