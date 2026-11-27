# The Catch-Up conjecture: Lean verification for N ≤ 16 and exact computation to N = 39

This repository contains Lean 4 work and computations around an open problem in Google
DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) collection,
`CatchUp.value_of_even_mul_succ_self_div_two`. It formalizes a conjecture of A. Isaksen,
M. Ismail, S. J. Brams and A. Nealen about their game Catch-Up: if 1 + 2 + ... + N = N(N+1)/2 is
even, the game played on the numbers {1, ..., N} is a draw under optimal play.

**This is not a proof of the conjecture.** The conjecture is a statement about every N, and it is
still open. What the repository contains is a Lean proof of the conjecture for every N ≤ 16, a
Lean proof of the easy complementary parity fact for every N, and an exact computer search that
finds no counterexample for N ≤ 39.

## The problem and what was done

Catch-Up is played with a set of positive integers. Both scores start at 0. The first player
takes one number. After that the players alternate turns: on a turn the player takes numbers one
at a time, must stay strictly behind before the last pick, and must stop as soon as their score
equals or exceeds the opponent's. A player who cannot catch up even by taking everything takes
everything and loses. When the numbers run out, the higher score wins and equal scores draw. The
paper computed the game on {1, ..., n} for n ≤ 20 by backward induction and conjectured that it
is a draw exactly when the total N(N+1)/2 is even, that is, when N ≡ 0 or 3 (mod 4).
formal-conjectures defines the optimal-play value by a recursive function `CatchUp.valueAux` and
states the even case as `value (Finset.Icc 1 N) = .draw`.

The work here:

1. **Audit of the statement.** The Lean model was compared with the rules of the paper. No
   mistranslation was found. See [PROOF.md](PROOF.md), Section 2.
2. **The conjecture for every N ≤ 16 (Lean).** `CatchUpCert.conj_le_16` is the upstream
   statement restricted to N ≤ 16. It is proved with a memoized certificate: a table of claims
   about positions, emitted by a C++ program and checked by a checker written in Lean.
   The checker is proved sound against the upstream `valueAux` (`check_sound`), so the
   certificate generator does not have to be trusted. The kernel checks the certificates with
   `decide +kernel`. For N = 16 the certificate has 4418 claims.
3. **An earlier direct proof for every N ≤ 12 (Lean).** `CatchUpOMA.conj_le_12` evaluates the
   game tree directly in the kernel, with a threshold evaluator proved equal to `valueAux`.
4. **The parity lemma, for every N (Lean).** `CatchUpOMA.value_ne_draw_of_odd`: if N(N+1)/2 is
   odd, the game is never a draw, because the final score difference always has the parity of
   the total. This is the easy direction. The file also contains `conj_iff` ("draw iff the total
   is even"), but `conj_iff` takes the conjecture as a hypothesis and is a trivial corollary, not
   progress on it.
5. **Exact computation to N = 39 (C++).** An exact minimax solver gives the value of the game for
   every N ≤ 25. It matches the published table for n ≤ 20 and gives new values for N = 21 to 25
   (first player wins at 21, 22 and 25; draws at 23 and 24). A threshold search confirms the
   conjecture for every N ≤ 39 with N(N+1)/2 even. No counterexample was found.

Pushing the Lean check to N ≤ 20 in one file used more than 16 GB of memory and was stopped.
Going further would need the certificates split across separately compiled modules.

## Status

- **Lean.** Items 2–4 are proved in Lean 4 against the unmodified upstream definitions
  (formal-conjectures at commit `9097e2f9`), with no `sorry` and no `native_decide`. All
  computation goes through `decide +kernel`, which is checked by the kernel's ordinary reduction.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem
  (`logs/axioms.log`). The open statement itself is not touched. Nothing was submitted to the
  formal-conjectures registry: the target is the full statement for all N, and the file has no
  variants that the results here would settle.
- **Paper proofs.** The statements, the soundness argument for the certificate checker, the
  parity lemma and the solver method are written out in [PROOF.md](PROOF.md). They have **not
  been checked by a human expert**.
- **AI assistance.** This work was found and written with the help of Claude (Anthropic).
  Separate Claude sessions re-verified the Lean builds and audited the claims adversarially,
  including a test that corrupted certificates are rejected, and one of them wrote an independent
  solver. They found no error. No expert in combinatorial game theory has checked it. See
  [CHECKS.md](CHECKS.md).
- **Computer checks.** The results for 16 < N ≤ 39 are computations, cross-checked between two
  solvers up to N = 25 but not formally verified.

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing

A C++ compiler and Python ≥ 3.10 (standard library only), from the repository root:

```bash
g++ -O2 -o scripts/solver2 scripts/solver2.cpp
scripts/solver2 0 25 29                        # exact values, N = 0..25 (2^29-entry table, 4.3 GB) -> logs/solver2_0_26.log
g++ -O2 -o scripts/solver3 scripts/solver3.cpp
scripts/solver3 22 34 28                       # threshold search, N = 22..34                -> logs/solver3_22_34.log
EVEN_ONLY=1 scripts/solver3 31 39 27           # even totals only; N = 39 takes ~18 min       -> logs/solver3_even_31_52.log
python3 -I independent-checks/cu.py            # reviewer's independent solver, N = 0..12   -> logs/independent_cu.log
```

The logged even-total run was started as `solver3 31 52 27` and stopped after N = 39.

Regenerating the certificate file (byte-identical to the committed one, `logs/gen_cert.log`):

```bash
g++ -O2 -o scripts/cert scripts/cert.cpp
python3 -I scripts/gen_cert_lean.py lean/CatchUpLean/Cert.lean 300 0 3 4 7 8 11 12 15 16
```

The raw claim lists go to `certs/` (or `$CERT_DIR`), which is not committed.

Lean (toolchain in `lean/lean-toolchain`, formal-conjectures at commit `9097e2f9`, which depends
on Mathlib `v4.33.1`):

```bash
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

`lake exe cache get` downloads the Mathlib build; the part of formal-conjectures that is needed is
compiled from source by `lake build`. Building `CatchUpLean.Cert` takes about 5 minutes and 9–13 GB
of memory (sampled peaks: 9.2 GB in the repository build, 13.1 GB in the original
`lake env lean` run).

## Contents

- `PROOF.md`: the game, the faithfulness check, the parity lemma, the direct evaluator, the
  certificate method and its soundness proof, the solvers, and the limits of the method
- `CHECKS.md`: the re-verifications and the adversarial audits
- `lean/`: the Lean 4 project (`CatchUpLean/Eval.lean`, `CatchUpLean/Parity.lean`,
  `CatchUpLean/Cert.lean`), depending on formal-conjectures; `lean/CertLib.lean.part` is the
  checker library that the generator copies to the top of `Cert.lean`
- `scripts/`: the exact solvers (`solver.cpp`, `solver2.cpp`, `solver3.cpp`), the certificate
  emitter (`cert.cpp`) and Lean generator (`gen_cert_lean.py`), and exploratory scripts
  (`interval_table.py`, `rules.py`, `rulestrat.py`, `thresh.py`, `treesize.py`,
  `treecount.cpp`, `peakrun.sh`)
- `logs/`: solver output, the certificate regeneration, the Lean build and axiom logs, and the
  records of the runs that ran out of memory
- `independent-checks/`: `cu.py`, a solver written by a separate reviewing session, sharing no
  code with `scripts/`

## References

- A. Isaksen, M. Ismail, S. J. Brams, A. Nealen, *Catch-Up: A Game in Which the Lead Alternates*,
  Game & Puzzle Design 1(2) (2015), 38–49. Preprint: MPRA Paper No. 108784,
  https://mpra.ub.uni-muenchen.de/108784/.
- S. J. Brams, *Game stymies AI*, Plus Magazine, https://plus.maths.org/game-stymies-ai.
- The Lean statement: formal-conjectures,
  [`FormalConjectures/Paper/CatchUpConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Paper/CatchUpConjecture.lean).
