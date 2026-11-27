# Independent checks

The Lean proofs and the computations were produced with the help of Claude, an AI model made by
Anthropic. To test them we ran further Claude sessions, each separate from the one that did the
work. One re-verified the Lean build; another was asked to audit the results adversarially and wrote
its own code to recompute them.

These checks were done by AI models, not by a specialist in the field, and should be read in that
light. The Lean results do not depend on them: they are checked by the Lean kernel. The SAT results
for N = 8 and N = 9 were not checked by anyone beyond the solver's own answer.

## First check: re-verification of the Lean file

A separate session compiled `Results.lean` against formal-conjectures (about 25 s) and confirmed
that `stabilityThreshold_le_half`, `stabilityThreshold_mono`, `K3`–`K6`, `three_le_K` and
`target_of_lowerBound` depend only on `[propext, Classical.choice, Quot.sound]`.

The build was repeated when this repository was assembled, as a standalone Lake project
pinned to formal-conjectures commit `9097e2f` (`logs/lean_build.log`, `logs/axioms.log`), with the
same result.

## Second check: adversarial audit

A fresh session with no prior context was asked to look for errors in the Lean file, the SAT
encoding and the claimed values.

**(A) Lean.** `Results.lean` refers to the upstream `Roommates.stabilityThreshold`, and the
conclusion of `target_of_lowerBound` is literally the upstream target (checked with `Iff.rfl`).
The proofs are sound. Low-severity remark: `target_of_lowerBound` adds little, since its hypothesis
is equivalent to the target once the upper bound is known. PROOF.md says so.

**(B) K(7) = 3.**

- The encoding `scripts/satgen.py` (without symmetry breaking) matches the upstream definitions:
  the number of its models, projected onto the preference variables (`independent-checks/count.py`),
  is 2, 48 and 120 for (N, k) = (3, 1), (4, 1), (5, 2). These are exactly the numbers of profiles
  with threshold K(N) found by the reviewer's own brute force (`independent-checks/bf.c`). The
  symmetry breaking (fixing agent 0's list) is valid.
- The UNSAT proof for (7, 3) was re-verified with drat-trim (`s VERIFIED`) and with lrat-check
  (`c VERIFIED`), 59,615 clauses.
- The reviewer's own encoding (`independent-checks/myenc.py`, pairwise-order variables, no symmetry
  breaking) is also UNSAT for (7, 3).

**(C) Prior work and faithfulness (medium).** The audit found formal-conjectures issue #7848 (the
statement came in through PR #7853), which calls "for all large N" an interpretation of the paper's
"for larger values", and noted that the paper models a general acceptability graph while the Lean
statement fixes the complete graph. It also found S. Levinstein's Zenodo preprint (24 November 2026,
AI-assisted, unrefereed), which claims K(2m+1) ≤ m for all m ≥ 3 and K(8) = 3, K(9) = 4,
K(11) = 5. It advised that the safe claim is that the formal target's pattern fails at N = 7, and
that the conjecture is not refuted by us without a proof for all large N. README.md and PROOF.md
were written accordingly, and the registry pull request #1883 with a Lean disproof is credited
there.

**(D) Low.** The N = 8 and N = 9 logs were empty while the runs were still going, and no `.lrat`
file is stored (it is regenerated on demand). Both runs have since finished UNSAT; neither has a
checked certificate, and the README and PROOF.md say so.

## Rerun of the independent code

When assembling this repository, the reviewer's programs in `independent-checks/` were run again
(`logs/independent_bf.log`, `logs/independent_myenc.log`, `logs/independent_count.log`): the brute force gives K(3), K(4), K(5)
= 2, 2, 3 over all (N−1)!^N profiles, and the independent encoding gives SAT for k = K(N) − 1 and
UNSAT for k = K(N) for N = 3, …, 6. The (7, 3) instance of the independent encoding did not finish
within the 20-minute limit used for this rerun, so for it we rely on the reviewer's reported UNSAT
(the main encoding's LRAT proof for N = 7 is checked separately, as above).
