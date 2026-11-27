# Moments of the number of stable matchings: Lean results for two firms

This repository contains Lean 4 work and computations around two open problems in Google
DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) collection,
`second_moment` and `second_moment_one_extra_worker` in `Arxiv.«1701.08900»`. They formalize a
conjecture of B. Pittel [arXiv:1701.08900](https://arxiv.org/abs/1701.08900): in a random matching
market with n firms and n + d workers, d ≥ 1 and d/n → 0, is the second moment of the number of
stable matchings of the same order as the square of its mean?

**This is not a solution of the open problem.** Both statements are about the limit n → ∞, and
nothing here proves or disproves them. What the repository contains is exact results for two
firms (proved in Lean), exact moments for small markets, and a Monte Carlo experiment that
suggests the conjecture may be false.

## The problem and what was done

There are n firms and m = n + d workers. Every agent ranks the whole other side, uniformly at
random and independently of everyone else. A matching gives every firm its own worker (m − n
workers stay unmatched), and it is stable if no firm and worker would both rather be together.
A worker who is unmatched is happy with any firm. Let S be the number of stable matchings. Pittel
proved first-moment asymptotics for E[S] (for d = 1, E[S] ~ e⁻¹ n / ln n) and conjectured that
E[S²] = O(E[S]²) when d ≥ 1 and d/n → 0. The formal-conjectures statements ask for C > 0 with
E[S²] ≤ C · E[S]² for all large n, for every such sequence d (`second_moment`) and for d = 1
(`second_moment_one_extra_worker`). In the balanced case d = 0 the analogous fact is a theorem of
Lennon and Pittel (2009).

The work here:

1. **Audit of the statement.** The Lean model (rankings, matchings as injections from firms to
   workers, blocking pairs, the uniform law, the hypotheses on d) was checked against the paper's
   TeX source. No mistranslation was found. See [PROOF.md](PROOF.md), Section 2.
2. **Two firms, any number of workers (Lean).** For n = 2 and every m ≥ 2, every preference
   profile has one or two stable matchings, two exactly on an explicit event C, and

   E[S] = 1 + 1/(4m(m − 1)),  E[S²] = 1 + 3/(4m(m − 1)).

   The proof is structural: it identifies the four possible stable matchings and counts C by
   explicit bijections. It does not enumerate profiles. Two firms are far from the asymptotic
   regime of the conjecture, so this says nothing about the open problem.
3. **Exact small cases (Lean).** For 2 firms with 2 workers, E[S] = 9/8 and E[S²] = 11/8; with 3
   workers (the one-extra-worker case), E[S] = 25/24 and E[S²] = 9/8. These are checked by the
   Lean kernel with `decide` on a computable count of stable matchings.
4. **A bridge lemma (Lean).** The upstream count `numStableMatchings` equals a computable count
   over injective functions, and the two moments equal finite averages of it.
5. **Exact moments of all small markets (C).** Exact rational E[S] and E[S²] for every market up
   to 4 firms and 6 workers (n ≤ 3 with m ≤ 7, n = 2 with m ≤ 8, n = 4 with m ≤ 6), cross-checked
   against a literal brute force over all profiles.
6. **Monte Carlo (heuristic only).** Sampling markets up to n = 800 suggests that with one extra
   worker the ratio E[S²]/E[S]² grows roughly like 0.55 · ln n (1.34 at n = 10, 2.57 at n = 100,
   3.9 ± 0.25 at n = 400). If that trend continued, the conjecture would be false. The balanced
   control stays flat near 1.33–1.36, as Lennon and Pittel's theorem predicts. This is sampling,
   with heavy tails and large error bars at the top end; it is not a proof of anything, and it is
   not evidence of the same kind as items 2–5.

## Status

- **Lean.** Items 2–4 are proved in Lean 4 against the unmodified upstream definitions
  (formal-conjectures at commit `9097e2f9`), with no `sorry` and no `native_decide`.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem
  (`logs/axioms.log`). The open statements themselves are not touched, and nothing was submitted
  anywhere.
- **Paper proofs.** The statement and proof of the two-firm theorem and the faithfulness analysis
  are in [PROOF.md](PROOF.md). They have **not been checked by a human expert**.
- **AI assistance.** This work was found and written with the help of Claude (Anthropic). Separate
  Claude sessions re-verified the Lean build and audited the claims adversarially, each writing
  its own brute force. They found no error. No expert in probability or matching theory has
  checked it. See [CHECKS.md](CHECKS.md).
- **Computer checks.** The exact tables in item 5 are computations, cross-checked but not
  formally verified. The Monte Carlo in item 6 is a heuristic.

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing

A C compiler and Python ≥ 3.10 (standard library only), from the repository root:

```bash
BIN=/tmp/moments scripts/run_exact.sh    # exact moments, all small markets -> logs/exact_raw.txt, logs/exact_moments.txt
python3 -I scripts/brute.py 2 3          # literal brute force over all profiles, one market
BIN=/tmp/mc scripts/run_mc.sh            # Monte Carlo sweep (hours)               -> logs/mc_*.txt
python3 -I independent-checks/brute_small.py   # reviewer's brute force: (2,2), (2,3), (3,2), (3,3)
python3 -I independent-checks/brute_n2.py      # reviewer's brute force: n = 2, m = 2..5, and the event C
```

Lean (toolchain in `lean/lean-toolchain`, formal-conjectures at commit `9097e2f9`, which depends
on Mathlib `v4.33.1`):

```bash
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

`lake exe cache get` downloads the Mathlib build; the part of formal-conjectures that is needed is
compiled from source by `lake build`.

## Contents

- `PROOF.md`: the problem, the faithfulness analysis, the two-firm theorem and its proof, the
  exact tables, the Monte Carlo experiment, and why the main question is out of reach
- `CHECKS.md`: the re-verifications and the adversarial audits
- `lean/`: the Lean 4 project (`PittelMoments/SmallCases.lean`, `PittelMoments/NTwo.lean`),
  depending on formal-conjectures
- `scripts/`: the exact moment computation (`moments.c`), the brute force (`brute.py`), the Monte
  Carlo enumerator (`mc.c`) and the scripts that run and summarize them
- `logs/`: exact tables, Monte Carlo output and summaries, the Lean build and axiom logs
- `independent-checks/`: two brute forces written by separate reviewing sessions, sharing no code
  with `scripts/`

## References

- B. Pittel, *On likely solutions of the stable matching problem with unequal numbers of men and
  women*, arXiv:1701.08900 (2017), https://arxiv.org/abs/1701.08900.
- C. Lennon, B. Pittel, *On the likely number of solutions for the stable marriage problem*,
  Combinatorics, Probability and Computing 18 (2009), 371–421.
- I. Ashlagi, Y. Kanoria, J. D. Leshno, *Unbalanced random matching markets: the stark effect of
  competition*, Journal of Political Economy 125 (2017), 69–98.
- The Lean statements: formal-conjectures,
  [`FormalConjectures/Arxiv/1701.08900/SecondMoment.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Arxiv/1701.08900/SecondMoment.lean).
