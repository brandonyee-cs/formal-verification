# Independent checks

The Lean proofs, the faithfulness analysis and the computations were found and written with the
help of Claude, an AI model made by Anthropic. To test them we ran further Claude sessions,
separate from the one that wrote the work. For each Lean file, one session re-verified the build
and another was asked to assume that the claims were wrong or overstated and to look for the
problem. The auditors wrote their own brute-force programs. They found no error and a few minor
points, described below.

These checks were done by AI models, not by a specialist in probability or matching theory, and
should be read in that light. The Lean theorems do not depend on them: they are checked by the
Lean kernel. None of the checks concern the open problem itself, which is untouched.

## First check: re-verification of the Lean builds

A separate session recompiled `SmallCases.lean` and, later, `NTwo.lean` against formal-conjectures
at commit `9097e2f9`.

- Both files compile without errors.
- `numStableMatchings_eq_countB`, `expected_2_2`, `secondMoment_2_2`, `expected_2_3`,
  `secondMoment_2_3`, `expected_two`, `secondMoment_two` and `numStableMatchings_two` depend only
  on `[propext, Classical.choice, Quot.sound]`.
- There is no `sorry`, `native_decide` or added `axiom`.

For this repository the files were moved into the standalone Lake project `lean/` (module names
`PittelMoments.SmallCases` and `PittelMoments.NTwo`, contents unchanged) and built again with
`lake build`; `lake env lean Axioms.lean` gives the same axioms for all fourteen theorems listed
there (`logs/lean_build.log`, `logs/axioms.log`).

## Second check: adversarial audit of the small cases

A fresh session with no prior context was given `SmallCases.lean`, the notes and the upstream
statement, and asked to find ways in which the claims fail or are overstated. Its verdict was that
the claims hold.

- The statements resolve to the upstream `StableMarriage.Unbalanced` definitions (checked with
  `pp.fullNames`), and the upstream checkout was clean at `9097e2f9`.
- The argument order is right: `2 3` means 2 firms and 3 workers, the one-extra-worker case; the
  reversed order gives 0.
- Its own brute force of the upstream blocking condition (`independent-checks/brute_small.py`)
  gives (2,2): 9/8, 11/8; (2,3): 25/24, 9/8; and (3,3): E[S] = 5027/3888, E[S²] = 7487/3888,
  matching the Lean values and the exact table.
- The model matches the paper (Gusfield–Irving blocking condition, uniform independent
  preferences). The asymptotic hypotheses were not audited beyond the definitions.
- (Minor) The files have no `module` header. This matters only if they were moved upstream.

## Third check: adversarial audit of the two-firm theorem

A second fresh session audited `NTwo.lean` and the paper proof (PROOF.md, Section 4). Verdict:
pass.

- The statements refer to the upstream definitions, m is the number of workers, and the theorems
  are not vacuous.
- Its own brute force (`independent-checks/brute_n2.py`) over all 16, 288, 9216 and 460800
  profiles for m = 2, 3, 4, 5 gives E[S] = 9/8, 25/24, 49/48, 81/80 and E[S²] = 11/8, 9/8, 17/16,
  83/80, equal to the formulas, and checks profile by profile that S = 2 if C holds and S = 1
  otherwise, with no mismatch.
- Steps 1–4 of the paper proof are sound.

It raised two minor points.

1. **(Low) Scope.** The profile-level statement S ∈ {1, 2} holds only for m ≥ 2; for m < 2 there
   is no matching and S = 0. **Addressed:** the scope is stated in the Lean docstring, the theorems
   are stated for `Profile 2 (k+2)` and `2 ≤ m`, and PROOF.md says so.
2. **(Cosmetic)** A stale docstring and unused `simp` arguments. **Fixed.**

## The brute forces in `independent-checks/`

Both programs were written by the reviewing sessions, not by the session that wrote the work, and
share no code with `scripts/`. They run standalone (Python ≥ 3.10, standard library only), and were
run again for this repository:

```
$ python3 -I independent-checks/brute_small.py   # n m #profiles ΣS ΣS² E[S] E[S²]
2 2 16 18 22 9/8 11/8
2 3 288 300 324 25/24 9/8
3 2 288 0 0 0 0
3 3 46656 60324 89844 5027/3888 7487/3888
$ python3 -I independent-checks/brute_n2.py      # m #profiles E[S] E[S²] (formula checks) mismatches
2 16 9/8 11/8 True True mismatch 0
3 288 25/24 9/8 True True mismatch 0
4 9216 49/48 17/16 True True mismatch 0
5 460800 81/80 83/80 True True mismatch 0
```

(`logs/independent_brute_small.log`, `logs/independent_brute_n2.log`; about 1 s and 10 s.)

## What was not checked

No check covered the Monte Carlo experiment beyond the validation described in PROOF.md,
Section 6, and its conclusion remains a heuristic.

## Reference

B. Pittel, *On likely solutions of the stable matching problem with unequal numbers of men and
women*, arXiv:1701.08900 (2017), https://arxiv.org/abs/1701.08900.
