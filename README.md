# Formal verification of research mathematics

Machine-checked partial results toward four open problems, written in Lean 4 with Mathlib. All four
problems come from Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) collection. Each folder
is a self-contained project with its own `README.md`, `PROOF.md` (statements and paper proofs),
`CHECKS.md` (independent checks), Lean project, scripts and logs.

**None of these is a complete proof, and none of them solves a listed open conjecture.** Every
result below is labelled with what kind of result it is. Lean theorems carry no `sorry` and depend
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. None uses
`native_decide`.

## Summary

| Project | Problem | Kind of result | What is proved in Lean | Registry |
|---|---|---|---|---|
| [pittel-stable-matching-moments](pittel-stable-matching-moments/) | Pittel's second-moment conjecture for random stable matchings (arXiv 1701.08900) | **Partial theorem** + bounded verification | For 2 firms and every m ≥ 2 workers: one or two stable matchings, E[S] = 1 + 1/(4m(m−1)), E[S²] = 1 + 3/(4m(m−1)) | None (the targets are asymptotic and open) |
| [roommates-stability-threshold](roommates-stability-threshold/) | Fanelli–Moscardelli stability threshold for roommates (ECAI 2025) | **Partial theorem** + bounded verification + independent confirmation | K(N) ≤ ⌈N/2⌉ for all N; K(N) ≤ K(N+1); K(3..6) = 2, 2, 3, 3. A SAT proof of K(7) = 3, checked by three proof checkers, agrees with a prior disproof by S. Levinstein | None (a disproof by S. Levinstein is already [PR #1883](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1883)) |
| [catch-up-conjecture-lean](catch-up-conjecture-lean/) | The Catch-Up conjecture (Isaksen, Ismail, Brams, Nealen) | **Bounded verification** | The conjecture for every N ≤ 16, via a certificate checker proved sound against the upstream definition; an odd total is never a draw, for every N. An exact solver confirms N ≤ 39 | None (no variants of the target) |
| [bayes-nash-security-games-lean](bayes-nash-security-games-lean/) | Polynomial-time Bayes–Nash equilibria in security games (V. Conitzer, arXiv 2610.08796) | **Statement validation** | The formal statement is faithful, and its equilibrium predicate is equivalent to the standard definition for every output; trivial special cases | None (the open question is untouched) |

### Kinds of result, strongest first

1. **Partial theorem**: a general theorem for a restricted case, such as two firms and every m.
2. **Bounded verification**: the statement is checked for finitely many cases.
3. **Independent confirmation**: an independent check of a result first obtained by someone else.
4. **Statement validation**: a check that the formal statement says what the paper says, with
   lemmas that make it usable. It says nothing about the answer.

Numerical or Monte Carlo experiments (for example the Pittel simulations, which suggest that
conjecture may be false) are reported in the projects as heuristic evidence only.

## Method

Each project followed the same steps:
- read the formal statement in plain words and check it against the source;
- compute small cases exactly, in integer or rational arithmetic, with proof certificates where a
  SAT solver was used;
- prove in Lean what could be proved;
- look as hard for counterexamples as for proofs;
- record what remains open.

Every Lean result was compiled and its axioms printed by a session other than the one that wrote
it. It was then audited by a separate session asked to find the ways it fails to prove what it
claims. The audits and the changes they led to are in each project's `CHECKS.md`.

## Status and responsibility

- **AI assistance.** This work was found and written with the help of Claude (Anthropic). The
  independent checks were also done by separate Claude sessions, not by specialists in the fields.
- **Human review.** None of the paper proofs has been checked by a human expert. The Lean proofs do
  not depend on any reviewer: they are checked by the Lean kernel against the stated definitions.
  Whether a formal statement faithfully captures the informal problem is a separate question,
  discussed in each project.
- **Prior work.** The roommates disproof is due to S. Levinstein (preprint
  [doi:10.5281/zenodo.24519727](https://doi.org/10.5281/zenodo.24519727)); the results in that
  folder are independent and agree with it.

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing

Each folder has a `lean/` Lake project with its toolchain pinned (`leanprover/lean4:v4.33.1`). Each
depends on formal-conjectures at commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.

```bash
cd <project>/lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

The Catch-Up certificate file needs about 13 GB of memory to check. The scripts and their
reproduction commands are listed in each project's README.

## License

MIT, see [LICENSE](LICENSE). Each project folder also carries its own copy of the MIT license.
