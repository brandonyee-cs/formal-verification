# The roommates stability threshold: what is proved and what is computed

*November 2026. Written with AI assistance (Claude) and not checked by a human expert; see
[CHECKS.md](CHECKS.md) for how it has been checked so far. Sections 2–3 are proved in Lean 4
(Section 5). Section 4 is computation.*

## 1. The statement

Notation follows `FormalConjecturesForMathlib/Combinatorics/Roommates.lean` in
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `9097e2f`).

- A *complete profile* on N agents gives each agent i a strict ranking of all agents, with i itself
  last. The *partner rank* rank_i(j) lies in 1..N−1 for j ≠ i, and rank_i(i) = N means single.
- A *matching* is any involution of the agents, so agents may be single.
- (i, j) is a *k-blocking pair* for μ if i ≠ j, μ(i) ≠ j, rank_i(j) + k ≤ rank_i(μ(i)) and
  rank_j(i) + k ≤ rank_j(μ(j)): both gain at least k places.
- K(N) = `Roommates.stabilityThreshold N` is the least k ≥ 1 such that every complete profile on N
  agents has a matching with no k-blocking pair. It is well defined because k = N + 1 always works.

The target `FanelliMoscardelli.stability_threshold_tight` is

```lean
theorem stability_threshold_tight :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2
```

where (N + 1)/2 is natural-number division, equal to ⌈N/2⌉.

**Faithfulness.** The paper's full text was not available to us; we read only the abstract, whose
definition of a k-blocking pair ("a pair of agents who could both improve their assigned partners
by at least k positions") agrees with the one above. The paper allows general acceptability graphs
and states the conjecture "for larger values". The formal statement fixes complete lists and reads
"larger values" as "all N ≥ N₀"; formal-conjectures issue #7848 (statement added in PR #7853)
calls this an interpretation. Everything below is about the formal statement.

## 2. Upper bound and monotonicity

**Theorem 1** (`stabilityThreshold_le_half`). K(N) ≤ ⌈N/2⌉ for every N ≥ 1.

*Proof.* Let k = ⌈N/2⌉ and t = N − k = ⌊N/2⌋. Among matchings in which every matched agent ranks
its partner at most t, choose one, μ, with as many matched agents as possible. A matched agent has
rank ≤ t ≤ k, so it can gain at most k − 1 places and is in no k-blocking pair. Two single agents
(rank N) that k-block rank each other at most N − k = t, so matching them would give an admissible
matching with more matched agents. Hence μ has no k-blocking pair. ∎

So the conjecture says that this simple bound is tight for all large N.

**Theorem 2** (`stabilityThreshold_mono`). K(N) ≤ K(N+1).

*Proof.* Given a profile on N agents, add a dummy agent whom everyone ranks just above being single
(the dummy's own list is arbitrary). Take a matching of the padded market with no k-blocking pair,
for k = K(N+1), and restrict it to the original agents, making anyone matched to the dummy single.
Moving from the restricted matching to the padded one, every original agent's rank of its partner
can only go up, so a k-blocking pair of the restriction would also k-block in the padded market. ∎

## 3. Small values and the reduction

**Theorem 3** (`K3`, `K4`, `K5`, `K6`). K(3) = 2, K(4) = 2, K(5) = 3, K(6) = 3.

*Proof.* The upper bounds are Theorem 1. For the lower bounds, explicit profiles with no
(K−1)-stable matching are checked by `decide` over all matchings: for N = 3 the library's
`cyclicThree`, for N = 4 a profile with no stable matching, for N = 5 a profile with no 2-stable
matching. K(6) ≥ K(5) is Theorem 2. ∎

**Corollary 4** (`three_le_K`). 3 ≤ K(N) for every N ≥ 5.

**Proposition 5** (`target_of_lowerBound`). The target follows from

  (H) ∃ N₀ ≥ 3, ∀ N ≥ N₀, ⌈N/2⌉ ≤ K(N).

This is immediate from Theorem 1, and given Theorem 1, (H) is equivalent to the target. So this
reduction adds little: it only isolates the lower bound as the open part. Section 4 shows (H) fails
at N = 7.

## 4. Computations

These are evidence, not part of the Lean development. All use exact integer arithmetic.

**Table 1. Exact values of K(N).**

| N | K(N) | ⌈N/2⌉ | Method (log) |
|---|---|---|---|
| 3 | 2 | 2 | brute force + SAT (`logs/n3to5.log`) |
| 4 | 2 | 2 | brute force + SAT (`logs/n3to5.log`) |
| 5 | 3 | 3 | brute force + SAT (`logs/n3to5.log`) |
| 6 | 3 | 3 | brute force over all 120⁵ ≈ 2.49·10¹⁰ profiles with agent 0's list fixed, + SAT (`logs/n6_k2.summary`, `logs/n6_k3.summary`) |
| 7 | 3 | 4 | SAT: "a profile with no 3-stable matching exists" is UNSAT (CaDiCaL 2.1.2, 2.6 s); LRAT proof with 59,615 clauses checked |
| 8 | 3 | 4 | SAT: UNSAT for k = 3 (CaDiCaL, 4,960 s; `logs/sat_n8_k3.log`); **no certificate checked** |
| 9 | 3 or 4 | 5 | SAT: UNSAT for k = 4 (CaDiCaL, 2,671 s; `logs/sat_n9_k4.log`); **no certificate checked** |

Lower bounds for N ≥ 7 come from Corollary 4.

- `scripts/search.c` enumerates every profile with agent 0's list fixed to 1 > 2 > … > N−1 (no loss
  of generality, by relabelling) and tests every matching. `scripts/run_n6.sh` shards N = 6 over
  agent 1's list.
- `scripts/satgen.py` encodes "there is a complete profile on N agents with no k-stable matching"
  (one clause per matching, saying some pair k-blocks it), with the same symmetry breaking.
  SAT ⇔ K(N) > k. `scripts/satsolve.py` runs CaDiCaL and re-verifies any model with
  `scripts/kstable.py`. The SAT answers agree with brute force for every (N, k) with N ≤ 6.
- For N = 7, k = 3 the LRAT proof was checked by `scripts/lratcheck.py` (a small RUP-only checker
  written for this project), and in the audit by drat-trim and lrat-check (Section 2 of CHECKS.md).
  The reviewing session's own encoding (`independent-checks/myenc.py`, no symmetry breaking) is also
  UNSAT for (7, 3).
- Simulated annealing (`scripts/anneal.c`) never found a profile without a 3-stable matching for
  N = 7, …, 11 (`logs/anneal_n10_11.log` for N = 10, 11).

So under the formal statement ⌈N/2⌉ is the right value for N ≤ 6 and the wrong one at N = 7 (with
a checked certificate) and at N = 8, 9 (unchecked). Since the target is only about all large N,
this does not disprove it. A disproof needs a general theorem such as K(2m+1) ≤ m for all large m,
and we have none: a candidate family of matchings for that bound is refuted by an N = 7 profile
(`scripts/satfamily.py`), and an approach through Tan's stable partitions was left open at the case
of "tight" odd cycles.

**Note: kernel-checking K(7) ≤ 3 in Lean.** We measured whether the N = 7 certificate could be
checked by the Lean kernel. The LRAT proof has 55,176 added clauses, 693,523 literals and 2,052,280
hint applications (16,483 deletions) over a CNF of 4,439 clauses. A structurally recursive RUP
checker (`scripts/lrat_kernel_bench_checker.lean`, input generated by `scripts/lrat2lean.py`) run
with `decide +kernel` took 89 s for the first 1,000 steps (5,179 hints), of which about 43 s was
elaborating the list literals, so roughly 9 ms of kernel time per hint. Extrapolated, the full proof
would need about **5 hours** of kernel time, plus elaborating a 15 MB literal, plus proofs that the
checker is sound and that the encoding matches the upstream definitions. We did not pursue it.

## 5. Lean formalization

The directory `lean/` is a Lean 4 (v4.33.1) project that depends on formal-conjectures at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (which pins Mathlib `v4.33.1`).
`lean/RoommatesThreshold/Results.lean` imports `FormalConjectures.Paper.ApproximatelyStableMatching`
and uses the upstream `Roommates.stabilityThreshold` directly. It proves, in namespace
`RoommatesThreshold`:

- `stabilityThreshold_le_half : 0 < n → stabilityThreshold n ≤ (n + 1) / 2` (Theorem 1)
- `stabilityThreshold_mono : stabilityThreshold n ≤ stabilityThreshold (n + 1)` (Theorem 2)
- `K3`, `K4`, `K5`, `K6` (Theorem 3) and `three_le_K : ∀ N ≥ 5, 3 ≤ stabilityThreshold N`
- `target_of_lowerBound`, whose conclusion is `type_of% @FanelliMoscardelli.stability_threshold_tight`

There is no `sorry`, no added axiom and no `native_decide`; the finite checks use `decide`.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each (`logs/axioms.log`).
The only build warning is an unused `simp` argument (`logs/lean_build.log`).

## 6. Prior and concurrent work

- S. Levinstein, *A Disproof of the Fanelli–Moscardelli Stability Threshold Conjecture for Odd
  Markets*, Zenodo preprint, 24 November 2026, doi:10.5281/zenodo.24519727. AI-assisted and
  unrefereed, with code at github.com/s66lem/conjectures. It claims K(2m+1) ≤ m for all m ≥ 3,
  which would make the target false, and reports K(7) = 3, K(8) = 3, K(9) = 4 and K(11) = 5.
- Open-math-agents registry pull request #1883
  (https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1883) contains a Lean disproof of
  the target; the registry's checker accepted it and it awaits human review.

We found both after obtaining the results above. Ours were obtained independently and agree with
theirs. We read the preprint's argument but did not verify it in full. Its graph G is the
mutual-top-m graph, which avoids the obstacle that refuted our top-(m+1) family. These steps look
sound to us: Lemma 2 (a stability criterion for matchings with exactly one single agent), the
reduction to "structure F" in Section 2, and the exchange step. We did not check the residual case
(Sumner's theorem on randomly matchable graphs, the good-arc lemmas, the counting bound and the
all-K₂ case).

Background: Irving (1985) gives an algorithm for stable roommates; Tan (1991) introduces stable
partitions; Abraham, Biró and Manlove (2005) study "almost stable" matchings with few blocking
pairs, a different notion that counts blocking pairs instead of measuring rank gains.

## References

- A. Fanelli and L. Moscardelli, *Approximately Stable Matching*, ECAI 2025, Frontiers in
  Artificial Intelligence and Applications 413, 3583–3590, doi:10.3233/FAIA251234.
- S. Levinstein, *A Disproof of the Fanelli–Moscardelli Stability Threshold Conjecture for Odd
  Markets*, Zenodo (2026), doi:10.5281/zenodo.24519727.
- R. W. Irving, An efficient algorithm for the "stable roommates" problem, *J. Algorithms* 6 (1985),
  577–595.
- J. J. M. Tan, A necessary and sufficient condition for the existence of a complete stable
  matching, *J. Algorithms* 12 (1991), 154–178.
- D. J. Abraham, P. Biró and D. F. Manlove, "Almost stable" matchings in the roommates problem,
  WAOA 2005, LNCS 3879, 1–14.
