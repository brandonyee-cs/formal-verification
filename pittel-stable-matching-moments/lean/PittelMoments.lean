import PittelMoments.SmallCases
import PittelMoments.NTwo

/-!
# Moments of the number of stable matchings: two firms and exact small cases

Side results for `Arxiv.«1701.08900».second_moment` and
`Arxiv.«1701.08900».second_moment_one_extra_worker` (formal-conjectures), stated against the
upstream definitions `StableMarriage.Unbalanced.expectedNumStableMatchings` and
`StableMarriage.Unbalanced.secondMomentNumStableMatchings`.

* `PittelMoments.SmallCases` (namespace `PittelSmall`): a computable-count bridge and the exact
  values for 2 firms with 2 and with 3 workers, checked by `decide`.
* `PittelMoments.NTwo` (namespace `PittelNTwo`): for 2 firms and every `m ≥ 2` workers,
  `S ∈ {1, 2}`, `E[S] = 1 + 1/(4m(m-1))` and `E[S^2] = 1 + 3/(4m(m-1))`, proved structurally.

The asymptotic open statements themselves are not touched.
-/
