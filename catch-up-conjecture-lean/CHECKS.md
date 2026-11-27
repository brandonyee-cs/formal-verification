# Independent checks

The Lean proofs, the faithfulness analysis and the computations were found and written with the
help of Claude, an AI model made by Anthropic. To test them we ran further Claude sessions,
separate from the one that wrote the work. For each Lean file, one session re-verified the build
and another was asked to assume that the claims were wrong or overstated and to look for the
problem. The auditors wrote their own solvers. They found no error and a few minor points,
described below.

These checks were done by AI models, not by a specialist in combinatorial game theory, and
should be read in that light. The Lean theorems do not depend on them: they are checked by the
Lean kernel. None of the checks concern the conjecture for general N, which is open.

## First check: re-verification of the direct evaluator and the parity lemma

A separate session recompiled `CatchUpEval.lean` (about 50 s) and `CatchUpParity.lean` against
formal-conjectures at commit `9097e2f9`.

- Both files compile without errors.
- `conj_le_12`, `valueAux_eq_ev`, the `value_Icc_*` theorems, `value_ne_draw_of_odd` and
  `conj_iff` depend only on `[propext, Classical.choice, Quot.sound]`. There is no
  `Lean.ofReduceBool`: `decide +kernel` is checked by the kernel, unlike `native_decide`.

## Second check: adversarial audit of the direct evaluator and the parity lemma

A fresh session with no prior context was given the two files, the notes and the upstream
statement, and asked to find ways in which the claims fail or are overstated. Its verdict was that
"target verified for all N ≤ 12, plus the odd-total parity lemma for all N" is accurate, with no
critical, major or moderate findings.

- The upstream `CatchUpConjecture.lean` is unmodified, nothing is redefined, and `conj_le_12` is
  the upstream statement word for word plus the hypothesis N ≤ 12.
- The fuel and no-duplicates side conditions are proved where they are used. The game semantics
  match the rules of Isaksen, Ismail, Brams and Nealen.
- Its own Python solver, which models a whole turn as a set of numbers rather than one pick at a
  time (`independent-checks/cu.py`), gives draws exactly at N ∈ {0, 3, 4, 7, 8, 11, 12} for
  N ≤ 12, agreeing with Lean.

It raised minor points.

1. **`conj_iff` is a trivial corollary.** It assumes the conjecture. The substantive cases are
   N = 3, 4, 7, 8, 11, 12. **Addressed:** README and PROOF.md say so.
2. **The files were checked with `lake env lean`, not as part of a build target.**
   **Addressed:** in this repository they are modules of the library `CatchUpLean` and are built
   with `lake build` (see below).
3. **(Cosmetic)** Duplicate helper lemmas (`best_eq` in `Eval.lean`, `best_eq'` in
   `Parity.lean`) and linter warnings. Left as they are: the names differ, so the files build
   together.

## Third check: re-verification of the certificate file

A separate session recompiled `CatchUpCert.lean` (N ≤ 16): exit code 0, 223 s, about 13 GB of
memory. `conj_le_16` elaborates to the upstream statement restricted to N ≤ 16,

```lean
∀ N ≤ 16, Even (N * (N + 1) / 2) → CatchUp.value (Finset.Icc 1 N) = CatchUp.Outcome.draw
```

and `conj_le_16` and `check_sound` depend only on `[propext, Classical.choice, Quot.sound]`.

## Fourth check: adversarial audit of the certificate checker

A fresh session audited `CatchUpCert.lean`. Verdict: no soundness issues; "Lean-verified for all
N ≤ 16" is accurate.

- `valueAux_eq_D` is kernel-checked, and `D` matches the upstream rules: the opening move, the
  continuation while behind, the hand-over on catching up, the cannot-catch-up loss and the end of
  the game.
- `check_sound` is by induction on the length of the remaining list, so there are no cycles to
  worry about. Missing or undecodable children make checks fail, not pass. Only checked claims are
  trusted, and both root claims are required (dropping either blocks `value_eq_draw_of_cert`).
- There is no `native_decide`, `ofReduceBool`, `implemented_by`, `opaque`, `axiom` or
  `set_option` in the file; all computation is `decide +kernel`.
- On a scratch copy for N = 7, the genuine certificate passes, and flipping any of 9 leaf claims
  or either root claim makes the kernel check fail.
- Its own Python transcription of the upstream `valueAux` gives draws at N = 0, 3, 4, 7, 8, 11,
  12 and wins for one side elsewhere.

It raised two minor points.

1. **(Cosmetic)** The generator wrote intermediate certificates to a hard-coded `/tmp` path.
   **Fixed:** the path is now `certs/` in the repository (or `$CERT_DIR`), and the emitter binary
   is `scripts/cert` (or `$CERT_BIN`). With the fix, the generator reproduces
   `lean/CatchUpLean/Cert.lean` byte for byte (`logs/gen_cert.log`).
2. **About 13 GB of memory** is the practical limit of the method in one file. This is stated in
   README and PROOF.md.

## The repository build

For this repository the three files were moved into the standalone Lake project `lean/` as the
modules `CatchUpLean.Eval`, `CatchUpLean.Parity` and `CatchUpLean.Cert`, with contents unchanged,
and built with `lake build` (exit code 0; `CatchUpLean.Cert` took 275 s). `lake env lean Axioms.lean` gives
`[propext, Classical.choice, Quot.sound]` for every theorem listed there (`logs/lean_build.log`,
`logs/axioms.log`).

## The solver in `independent-checks/`

`cu.py` was written by a separate reviewing session, not by the session that wrote the work, and
shares no code with `scripts/`. It plays a whole turn at once: a turn is a set X of remaining
numbers whose sum reaches the deficit while the sum without its largest element does not (or
everything, if the player cannot catch up). It runs standalone (Python ≥ 3.10, standard library
only, about 1 s), and was run again for this repository (`logs/independent_cu.log`):

```
$ python3 -I independent-checks/cu.py    # N, T_N even?, value (1 = P1 wins, 0 = draw, -1 = P2 wins)
0 True 0
1 False 1
2 False 1
3 True 0
4 True 0
5 False 1
6 False 1
7 True 0
8 True 0
9 False -1
10 False -1
11 True 0
12 True 0
```

This agrees with `scripts/solver2.cpp` for every N ≤ 12.

## What was not checked

No reviewer re-ran the long solver3 searches for 25 < N ≤ 39. Those results come from one
program, and are computations, not proofs.

## Reference

A. Isaksen, M. Ismail, S. J. Brams, A. Nealen, *Catch-Up: A Game in Which the Lead Alternates*,
Game & Puzzle Design 1(2) (2015), 38–49; MPRA Paper No. 108784.
