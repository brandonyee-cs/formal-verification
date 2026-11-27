# Independent checks

The Lean proofs, the faithfulness analysis and the enumerator were found and written with the help
of Claude, an AI model made by Anthropic. To test them we ran further Claude sessions, separate
from the one that wrote the work. One re-verified the Lean build; another was asked to assume
that the claims were wrong or overstated and to look for the problem. It found no error, and
one gap, which has been closed, as described below.

These checks were done by AI models, not by a specialist in game theory or complexity, and should
be read in that light. The Lean theorems do not depend on them: they are checked by the Lean
kernel. None of the checks concern the open problem itself, which is untouched.

## First check: re-verification of the Lean build

A separate session recompiled `DefenderBR.lean` and `Instance.lean` against formal-conjectures at
commit `9097e2f9`.

- Both files compile without errors.
- Every theorem depends only on `[propext, Classical.choice, Quot.sound]`; two helper lemmas use
  fewer axioms.
- There is no `sorry`, `native_decide` or added `axiom`.

For this repository the files were moved into the standalone Lake project `lean/` (module names
`BayesNashSecurityGames.DefenderBR` and `BayesNashSecurityGames.Instance`, contents unchanged) and
built again with `lake build`; `lake env lean Axioms.lean` gives the same axioms
(`logs/lean_build.log`, `logs/axioms.log`).

## Second check: adversarial audit

A fresh session with no prior context was given the Lean files, the notes and the upstream
statement, and asked to find ways in which the claims fail or are overstated. It checked the
claims against the unmodified upstream definitions (a clean checkout of formal-conjectures at
`9097e2f9`). Its verdict was that the claims hold and that the description of the work ("a
faithfulness lemma, existence for r = 0 and r = |T|, and a concrete instance") is accurate. It
raised four points.

1. **(Medium) The faithfulness theorem covered only outputs of a canonical shape.** At the time,
   the equivalence between `IsBayesNash` and the standard equilibrium conditions
   (`isBayesNash_mkOutput_iff_optimal`, Theorem 3 of PROOF.md) was proved only for outputs of the
   form `mkOutput g c a`. An arbitrary list could in principle satisfy `IsBayesNash` without being
   of that form. The auditor proved in a scratch file (`logs/reviewer_All.lean.txt`) that this
   cannot happen: the length clauses force every output satisfying `IsBayesNash` to be
   `mkOutput g c a` for its own entries.
   **Fixed:** this was added as `eq_mkOutput_of_isBayesNash`, together with the corollary
   `isBayesNash_iff_optimal`, which states the equivalence for every output (Theorem 4 of
   PROOF.md). Both compile, with axioms `[propext, Classical.choice, Quot.sound]`.
2. **(Low to medium) Marginals versus mixtures.** The defender optimizes over coverage marginals
   in F_r. That every such marginal vector comes from a distribution over r-subsets is asserted
   upstream and is standard, but it is not proved here. Zero-prior types are also required to
   best-respond (an interim BNE), which is documented upstream. Both points are stated in
   PROOF.md, Section 2.
3. **(Low) The cases r = 0 and r = |T| are trivial.** The defender clause is vacuous there, so the
   result has no strategic content. It was correctly labelled as such, and is labelled so here.
4. **(Low) The non-uniqueness example relies on a tie.** The family of equilibria for g₀ exists
   because the defender's two marginal gains are exactly equal, so g₀ is not generic. This is
   stated in PROOF.md, Section 5, and in the README.

## Reference

V. Conitzer, *Open problem: Computing Bayes–Nash equilibrium in simple security games*,
arXiv:2610.08796 (2026), https://arxiv.org/abs/2610.08796.
