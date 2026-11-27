# Bayes–Nash equilibria in security games: a Lean audit and special cases

This repository contains Lean 4 work around the open problem `exists_isPolyTime_bayesNash` in
Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
collection, which formalizes V. Conitzer's question
[arXiv:2610.08796](https://arxiv.org/abs/2610.08796): can a Bayes–Nash equilibrium of a Bayesian
simple security game be computed in polynomial time?

**This is not a solution of the open problem.** Nothing here bears on whether a polynomial-time
algorithm exists. What the repository contains is an audit of the Lean statement, Lean proofs that
its equilibrium predicate means what it should, and some easy special cases.

## The problem and what was done

In a Bayesian simple security game a defender covers r of the targets T, and an attacker, whose
type θ is drawn from a known prior, learns θ and attacks one target. Each player's payoff at a
target depends only on whether that target is covered, and coverage helps the defender and hurts
the attacker. Conitzer asks whether a Bayes–Nash equilibrium (BNE) can be computed in time
polynomial in the size of the payoff tables. The paper notes that computing a Stackelberg
strategy in this model is NP-hard, and that a non-Bayesian variant with several attacker resources
is solvable in polynomial time. With a single attacker type, polynomial-time algorithms follow from
known results (Korzhyk et al. 2011). The Bayesian question was first posed in 2015 and is open.

The formal-conjectures statement asks for a function from games to outputs (coverage marginals
and one attack distribution per type) that is computable by a polynomial-time Turing machine
(Mathlib's `TM2ComputableInPolyTime`) and returns an output satisfying the predicate
`IsBayesNash` on every valid game. The work here:

1. **Audit of the statement.** The encoding, the polynomial-time notion, the validity conditions
   and `IsBayesNash` were checked against the paper. No mistranslation was found. Two minor
   deviations (zero-prior types must also best-respond; list entries are read with defaults) are
   harmless. See [PROOF.md](PROOF.md), Section 2.
2. **`IsBayesNash` is the standard BNE condition (Lean).** `IsBayesNash` checks the defender's
   optimality only through a pairwise "shift coverage from t to s" condition. For every output,
   `IsBayesNash` holds if and only if the output is a well-shaped coverage vector c and attack
   profile a such that every type plays only best responses and c maximizes the defender's
   expected utility over all feasible coverage vectors.
3. **The cases r = 0 and r = |T| (Lean).** For every valid game with r = 0 or r = |T| an output
   satisfying `IsBayesNash` exists. These cases are trivial: the defender has a single feasible
   coverage vector, so only the attacker's best response has to be chosen.
4. **A concrete instance (Lean).** A game with 2 targets and 2 attacker types in which every
   coverage (x, 1 − x) with 1/3 ≤ x ≤ 7/8 is part of a BNE with the same attacks. So the defender's
   equilibrium coverage need not be unique. This relies on an exact tie in the defender's payoffs,
   so the game is not generic.
5. **Exact enumeration (Python).** An exact rational support enumeration found a BNE in every one
   of 350 small random games (up to 4 targets and 3 types), each candidate re-checked against a
   transcription of `IsBayesNash`. Existence is classical (Nash), so this is a sanity check of the
   formal definitions, not evidence about complexity.

## Status

- **Lean.** Items 2–4 are proved in Lean 4 against the unmodified upstream definitions
  (formal-conjectures at commit `9097e2f9`), with no `sorry` and no `native_decide`.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem
  (`logs/axioms.log`). The open statement `exists_isPolyTime_bayesNash` itself is not touched, and
  nothing was submitted anywhere.
- **Paper proofs.** The statements and proofs of what the Lean files prove, the faithfulness
  analysis, and a discussion of why the main question is out of reach are in
  [PROOF.md](PROOF.md). They have **not been checked by a human expert**.
- **AI assistance.** This work was found and written with the help of Claude (Anthropic). Separate
  Claude sessions re-verified the Lean build and audited the claims adversarially. The audit found
  that the faithfulness theorem covered only outputs of a canonical shape; this was fixed by
  proving it for all outputs. No expert in game theory or complexity has checked it. See
  [CHECKS.md](CHECKS.md).
- **Computer checks.** The enumeration in item 5 is evidence, not proof.

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing

Python ≥ 3.10, standard library only:

```bash
python3 -I scripts/bne_enum.py 0 200 5      # small-integer games, zero priors allowed (~10 min) -> logs/bne_enum_seed0.log
python3 -I scripts/bne_enum.py 1 150 1000   # generic games, positive priors (~15 min)        -> logs/bne_enum_generic_seed1.log
```

Lean (toolchain in `lean/lean-toolchain`, formal-conjectures at commit `9097e2f9`, which depends
on Mathlib `v4.33.1`):

```bash
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

`lake exe cache get` downloads the Mathlib build; the part of formal-conjectures that is needed is
compiled from source by `lake build`.

## Contents

- `PROOF.md`: statements and proofs of the Lean results, the faithfulness analysis, the
  computer checks, and why the main question is out of reach
- `CHECKS.md`: the re-verification and the adversarial audit, and the fix it led to
- `lean/`: the Lean 4 project (`BayesNashSecurityGames/DefenderBR.lean`,
  `BayesNashSecurityGames/Instance.lean`), depending on formal-conjectures
- `scripts/`, `logs/`: the exact enumerator, its logs, the Lean build and axiom logs, and the
  auditor's scratch Lean file (`logs/reviewer_All.lean.txt`)

## References

- V. Conitzer, *Open problem: Computing Bayes–Nash equilibrium in simple security games*,
  arXiv:2610.08796 (2026), https://arxiv.org/abs/2610.08796.
- The Lean statement: formal-conjectures,
  [`FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean).
