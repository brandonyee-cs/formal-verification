# The roommates stability threshold: Lean bounds and exact small values

This repository contains Lean 4 proofs and computer checks about the stability threshold K(N) of
A. Fanelli and L. Moscardelli, *Approximately Stable Matching*, ECAI 2025
([doi:10.3233/FAIA251234](https://doi.org/10.3233/FAIA251234)), in the form stated in Google
DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) as
`FanelliMoscardelli.stability_threshold_tight`. It does **not** settle that conjecture. A
disproof for odd N has been claimed by someone else (see *Prior and concurrent work* below), and our
results agree with it.

## The problem and the result

N agents each rank all the others strictly (complete preference lists); being single is ranked last.
A matching may leave agents single. A pair (i, j) *k-blocks* a matching if both i and j would move
up at least k places in their own lists by pairing with each other. K(N) is the least k ≥ 1 such
that every such profile on N agents has a matching with no k-blocking pair. Fanelli and Moscardelli
conjecture, in the formalized reading, that

  ∃ N₀ ≥ 3, ∀ N ≥ N₀, K(N) = ⌈N/2⌉.

**Proved in Lean** (against the upstream definitions, no `sorry`):

- K(N) ≤ ⌈N/2⌉ for every N ≥ 1, so the conjecture is the claim that this easy bound is tight;
- K(N) ≤ K(N+1) for every N;
- K(3), K(4), K(5), K(6) = 2, 2, 3, 3, and 3 ≤ K(N) for every N ≥ 5;
- the target follows from the hypothesis "∃ N₀ ≥ 3, ∀ N ≥ N₀, ⌈N/2⌉ ≤ K(N)". Given the upper
  bound, this hypothesis is just a restatement of the target, so this reduction adds little.

**Computed** (evidence, not Lean proofs):

| N | K(N) | ⌈N/2⌉ | how |
|---|---|---|---|
| 3–6 | 2, 2, 3, 3 | 2, 2, 3, 3 | exhaustive search (N = 6: all 120⁵ normalized profiles) and SAT; also in Lean |
| 7 | **3** | 4 | SAT (UNSAT for k = 3), LRAT proof checked by three separate checkers; independent encoding agrees |
| 8 | **3** | 4 | SAT (UNSAT for k = 3); **no proof certificate checked** |
| 9 | **3 or 4** | 5 | SAT (UNSAT for k = 4); **no proof certificate checked** |

The lower bounds K(N) ≥ 3 for N = 7, 8, 9 are the Lean theorem above. So under the formal
statement, the conjectured value ⌈N/2⌉ is wrong at N = 7 (with a checked certificate) and, by
unchecked SAT runs, at N = 8 and 9. Because the conjecture is only about *all large* N, these
finite cases do not disprove it by themselves.

## Prior and concurrent work

- S. Levinstein, *A Disproof of the Fanelli–Moscardelli Stability Threshold Conjecture for Odd
  Markets*, Zenodo preprint, November 2026,
  [doi:10.5281/zenodo.24519727](https://doi.org/10.5281/zenodo.24519727). It is described as
  AI-assisted and is not refereed. It claims K(2m+1) ≤ m for all m ≥ 3, which would make the
  formal target false. It also reports K(7) = 3, K(8) = 3, K(9) = 4 and K(11) = 5.
- The open-math-agents registry pull request
  [#1883](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1883) contains a Lean
  disproof of `FanelliMoscardelli.stability_threshold_tight`. The registry's checker accepted it,
  and it is awaiting human review.

We found both after obtaining the results here. Our work is independent of them and agrees with
them wherever they overlap. We did not try to duplicate the disproof.

## Faithfulness caveat

We could read only the abstract of the paper. As far as we can tell, the paper works with general
acceptability graphs and states the conjecture "for larger values" of N. The formal statement fixes
complete preference lists (the complete graph) and reads "larger values" as "all N ≥ N₀".
formal-conjectures issue [#7848](https://github.com/google-deepmind/formal-conjectures/issues/7848)
discusses whether this reading is right. Everything here is about the formal statement. If the
authors meant a different model, our numbers say nothing about it.

## Status

- **Lean.** The results above are proved in Lean 4 against the upstream definitions in
  formal-conjectures (commit `9097e2f`). There is no `sorry` and no `native_decide`, and the
  small cases use kernel `decide`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
  for every main theorem (`logs/axioms.log`).
- **Computations.** K(7) = 3 rests on a SAT solver's UNSAT answer whose LRAT proof was verified by
  our own checker, by drat-trim and by lrat-check. A separately written encoding also gives UNSAT.
  K(8) = 3 and K(9) ≤ 4 rest on single CaDiCaL runs with no checked certificate.
- **Paper proofs.** The arguments in [PROOF.md](PROOF.md) have **not been checked by a human
  expert**.
- **AI assistance.** This work was done with the help of Claude (Anthropic). Separate Claude
  sessions re-checked the Lean build and audited the results, one of them asked to look for errors.
  It found none in the results and raised the prior-work and faithfulness points above. See
  [CHECKS.md](CHECKS.md).

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing the checks

C compiler, Python ≥ 3.10 (standard library only), and CaDiCaL (the scripts use the copy shipped
with the Lean toolchain, `~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/cadical`):

```bash
cd scripts && gcc -O3 -o search search.c && ./search 5 2     # exhaustive, N <= 5 (~1 s)
sh scripts/run_n6.sh                                         # exhaustive N = 6 (~6 min on 4 cores)
python3 scripts/satsolve.py 7 3                              # UNSAT <=> K(7) <= 3 (~3 s)
python3 scripts/satgen.py 7 3 x.cnf && cadical --lrat=true --binary=false x.cnf x.lrat \
  && python3 scripts/lratcheck.py x.cnf x.lrat               # LRAT check for N = 7
python3 scripts/satsolve.py 8 3 7200                         # ~80 min
python3 scripts/satsolve.py 9 4 7200                         # ~45 min
```

Lean (toolchain in `lean/lean-toolchain`, formal-conjectures pinned in `lean/lakefile.toml`):

```bash
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

## Contents

- `PROOF.md`: the statements, proofs of the Lean results, the computations, the kernel-check
  feasibility estimate for N = 7, and prior work
- `CHECKS.md`: the re-verification and the audit, and what they found
- `lean/`: the Lean 4 project (`RoommatesThreshold/Results.lean`, `Axioms.lean`)
- `scripts/`, `logs/`: exhaustive search, SAT encoding and LRAT checker, heuristics, and logs
- `independent-checks/`: brute force and a SAT encoding written by a separate reviewing session,
  sharing no code with `scripts/`

## References

- A. Fanelli and L. Moscardelli, *Approximately Stable Matching*, ECAI 2025, Frontiers in Artificial
  Intelligence and Applications 413, 3583–3590, doi:10.3233/FAIA251234.
- S. Levinstein, *A Disproof of the Fanelli–Moscardelli Stability Threshold Conjecture for Odd
  Markets*, Zenodo (2026), doi:10.5281/zenodo.24519727.
- Google DeepMind, formal-conjectures, `FormalConjectures/Paper/ApproximatelyStableMatching.lean`.
