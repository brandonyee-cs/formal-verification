# Moments of the number of stable matchings: Lean results for two firms

This document states and proves what the Lean files prove, records the faithfulness check of the
formal statement against Pittel's paper, and describes the computations. **It does not solve the
open problem.** Pittel's conjecture is about n → ∞; everything proved here concerns two firms or
finitely many small markets. The Monte Carlo experiment in Section 6 is a heuristic, not evidence
of the same kind as Sections 3–5.

## 1. The problem

There are n firms and m = n + d workers, d ≥ 0. Each firm ranks all workers and each worker ranks
all firms, by strict orders drawn uniformly at random and independently. A matching μ assigns to
each firm i a worker μ(i), injectively, so m − n workers are unmatched. A pair (i, j) with
μ(i) ≠ j **blocks** μ if firm i ranks j above μ(i) and either j is unmatched or j ranks i above its
own partner. μ is **stable** if no pair blocks it. Let S = S(n, m) be the number of stable
matchings.

Pittel (arXiv:1701.08900, Theorem 1.3) proved first-moment asymptotics in the unbalanced case: for
d = 1, E[S] ~ e⁻¹ n / ln n, and E[S] → ∞ exactly when d/n → 0. On page 7, right after the theorem,
he writes: "We conjecture that for n₂/n₁ → 1, i.e. when E[S(n)] → ∞, the second order moment
E[S²(n)] = O(E²[S(n)])." In the balanced case d = 0 the analogous statement is a theorem of Lennon
and Pittel (2009), who showed E[S²] = Θ((n ln n)²) = Θ(E[S]²).

The formal-conjectures entries (file `FormalConjectures/Arxiv/1701.08900/SecondMoment.lean`) are:

```lean
theorem second_moment (d : ℕ → ℕ) (hd : ∀ n, 1 ≤ d n)
    (hd_limit : Tendsto (fun n ↦ (d n : ℝ) / n) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      secondMomentNumStableMatchings n (n + d n) ≤
        C * (expectedNumStableMatchings n (n + d n)) ^ 2

theorem second_moment_one_extra_worker :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      secondMomentNumStableMatchings n (n + 1) ≤
        C * (expectedNumStableMatchings n (n + 1)) ^ 2
```

The second is the case d ≡ 1 of the first. Both are open. Equivalently, the conjecture says that
the ratio E[S²]/E[S]² stays bounded.

## 2. Faithfulness of the formalization

The definitions are in `FormalConjecturesForMathlib/Combinatorics/StableMarriage/Unbalanced.lean`.

- `Profile n m` holds `firmRank : Fin n → Perm (Fin m)` and `workerRank : Fin m → Perm (Fin n)`,
  lower rank meaning preferred. Every complete strict profile appears exactly once.
- `Matching n m := Fin n ↪ Fin m`: every firm matched, m − n workers unmatched.
- `IsBlockingPair p μ i j`: μ i ≠ j, firm i ranks j above μ i, and for every k with μ k = j, worker
  j ranks i above k. The last clause is vacuous when j is unmatched.
- `numStableMatchings p` is the number of μ with no blocking pair. The law is
  `PMF.uniformOfFintype (Profile n m)`, and `expectedNumStableMatchings`,
  `secondMomentNumStableMatchings` are the integrals of S and S² against it, that is, the averages
  of S and S² over all (m!)ⁿ (n!)ᵐ profiles.

Comparison with the paper (arXiv e-print v2, TeX source read, lines 175–255):

- The paper follows Gusfield–Irving with n₁ < n₂: men [n₁], women [n₂]. A stable matching is an
  injection from men to women with no pair (m, w) such that m prefers w to his partner and, if w
  is matched, w prefers m to hers. Lean firms are the paper's men (the smaller side, all matched)
  and Lean workers are the women. The blocking conditions agree.
- Preferences are independent and uniform on both sides in both.
- Counting only firm-covering injections loses nothing: with complete lists and n ≤ m, a matching
  that leaves a firm unmatched also leaves a worker unmatched, and that pair blocks.
- The hypotheses d n ≥ 1 and d n / n → 0 are n₂ > n₁ and n₂/n₁ → 1. The O(·) becomes
  ∃ C > 0, eventually ≤. C may depend on the sequence d, which is the natural reading.

Minor remarks, none a mistranslation: the paper's gloss "i.e. when E[S] → ∞" is equivalent to
d/n → 0 by Theorem 1.3; at n = 0 the Lean quotient (d 0 : ℝ)/0 is 0, which is irrelevant to an
asymptotic hypothesis. **No mistranslation was found.**

## 3. A computable count, and the cases (2, 2) and (2, 3)

**Lemma 1 (bridge).** For every profile p, `numStableMatchings p` equals the number of injective
functions f : Fin n → Fin m that satisfy the Boolean form of the stability condition. Hence

E[S] = (Σ_p countB p) / |Profile n m|,  E[S²] = (Σ_p (countB p)²) / |Profile n m|,

and |Profile n m| = (m!)ⁿ (n!)ᵐ.

*Proof.* The map μ ↦ (μ as a function) is a bijection from stable embeddings to injective functions
satisfying the condition, and the condition unfolds to `IsStable`. The integrals against the
uniform PMF on a finite type are finite averages. ∎

(The re-encoding is needed for computation: the `Fintype` instance on `Fin n ↪ Fin m` goes through
classical choice and does not reduce in the kernel.)

**Proposition 2.** E[S(2, 2)] = 9/8, E[S(2, 2)²] = 11/8, E[S(2, 3)] = 25/24, E[S(2, 3)²] = 9/8.

*Proof.* The sums are Σ countB = 18 and Σ countB² = 22 over the 16 profiles of (2, 2), and 300 and
324 over the 288 profiles of (2, 3). These are evaluated by `decide` in the Lean kernel. ∎

Both are special cases of Theorem 3 below and agree with it.

## 4. Two firms and any number of workers

**Theorem 3.** Let n = 2 and m ≥ 2. For every profile, S ∈ {1, 2}, and S = 2 exactly on the event C
defined below. Consequently

E[S] = 1 + 1/(4m(m − 1)),  E[S²] = 1 + 3/(4m(m − 1)),

that is, P(S = 2) = 1/(4m(m − 1)).

In particular E[S²]/E[S]² → 1 as m → ∞ with n = 2. This is a regime where the number of firms is
fixed, far from the conjecture's regime n → ∞, so it says nothing about the open problem.

*Notation.* Call the firms A (index 0) and B (index 1). Let a₀, a₁ be A's first and second choices
and b₀, b₁ be B's. Write prefB(w) if worker w ranks B above A. A matching is a pair (x, y) with
x ≠ y: A gets x, B gets y.

*Step 1 (stability of a pair).* (x, y) is stable iff every worker that A ranks above x is y and
prefers B, and every worker that B ranks above y is x and prefers A. Indeed, a worker j ≠ x that A
ranks above x blocks with A unless j is matched and prefers its partner to A; the only matched
worker other than x is y, whose partner is B.

*Step 2 (four candidates).* If (x, y) is stable, then A ranks at most one worker above x, so
x ∈ {a₀, a₁}, and likewise y ∈ {b₀, b₁}. So S counts the stable ones among the four distinct
candidates (aᵢ, bⱼ):

- (a₀, b₀) is stable iff a₀ ≠ b₀;
- (a₁, b₀) is stable iff a₁ ≠ b₀, a₀ = b₀ and prefB(a₀);
- (a₀, b₁) is stable iff a₀ ≠ b₁, b₀ = a₀ and not prefB(b₀);
- (a₁, b₁) is stable iff a₁ ≠ b₁, a₀ = b₁, prefB(a₀), b₀ = a₁ and not prefB(b₀).

*Step 3 (case split).* If a₀ = b₀, exactly one of (a₁, b₀) and (a₀, b₁) is stable, decided by
prefB(a₀), and S = 1. If a₀ ≠ b₀, (a₀, b₀) is stable, the two mixed candidates fail, and (a₁, b₁)
is stable iff

C :  a₀ = b₁, b₀ = a₁, prefB(a₀) and not prefB(b₀).

C forces a₀ ≠ b₀, so in all cases S = 1 + [C], and S² = 1 + 3[C].

*Step 4 (counting C).* There are N = (m!)² 2ᵐ profiles. Fix A's ranking. The B-rankings whose
first two choices are a₁ and a₀ number (m − 2)!: every off-diagonal fibre of τ ↦ (τ⁻¹(0), τ⁻¹(1))
has the same size (translate by a permutation), and the m(m − 1) fibres partition the m!
permutations. The workers' rankings with a prescribed order at the two distinct workers a₀ and a₁
number 2^(m−2). So #C = m! (m − 2)! 2^(m−2), and #C · 4m(m − 1) = N. Therefore
E[S] = (N + #C)/N = 1 + 1/(4m(m − 1)) and E[S²] = (N + 3#C)/N = 1 + 3/(4m(m − 1)). ∎

For m < 2 there is no injection Fin 2 → Fin m and S = 0; Theorem 3 does not cover that case.

## 5. Exact moments of small markets

`scripts/moments.c` computes E[S] and E[S²] exactly (as integer numerators over a common
denominator, in 128-bit arithmetic) for every market up to 4 firms and 6 workers. It conditions on
the firms' rankings F. Given F, whether an unmatched worker blocks is determined by F, and the
workers' constraints are independent, so P(μ and ν both stable | F) is a product over workers of
counts of permutations of Fin n meeting that worker's constraints. Firm 0's ranking is fixed to the
identity by symmetry, and the other firms' rankings are enumerated as a multiset with multinomial
weights.

It was cross-checked against `scripts/brute.py`, a literal brute force over all profiles and all
injections that follows the Lean definitions, on (1,1), (1,3), (2,2), (2,3), (2,4) and (3,3); the
values agree exactly. The full table is `logs/exact_moments.txt`. A selection:

| n | m | d | E[S] | E[S²] | E[S²]/E[S]² |
|---|---|---|---|---|---|
| 2 | 3 | 1 | 25/24 | 9/8 | 1.0368 |
| 3 | 3 | 0 | 5027/3888 | 7487/3888 | 1.1519 |
| 3 | 4 | 1 | 4277/3888 | 40657/31104 | 1.0802 |
| 4 | 4 | 0 | 986579/663552 | 253504541/95551488 | 1.2001 |
| 4 | 5 | 1 | 290303809/248832000 | 3652990993/2388787200 | 1.1235 |
| 4 | 6 | 2 | 222893/204800 | 136951138559/107495424000 | 1.0756 |

For n = 2 the table matches Theorem 3 for m = 2, …, 8 (it was how the formula was found). The
first unbalanced case with five firms, (5, 6), would need about 1.1 · 10¹⁰ firm tuples and was not
attempted. These values are far from the asymptotic regime and cannot confirm or refute an
"eventually" statement.

## 6. Monte Carlo (heuristic only)

**This section is a heuristic.** It is sampling, not a proof, and should not be read as evidence
of the kind in Sections 3–5.

`scripts/mc.c` samples random profiles and lists all stable matchings of each: firm-proposing
deferred acceptance gives the firm-optimal matching, and a breadth-first search over
break-marriage moves (McVitie–Wilson, Gusfield–Irving) finds the rest, each re-checked for
stability. It was checked against brute force on 2000 random instances each of (3,4), (4,5),
(5,6), (6,7), (6,6) (`logs/mc_check.txt`) and against the exact value at (4,5). Pooled estimates
(`logs/mc_summary.txt`; raw sums in `logs/mc_all.txt`):

| n | balanced, d = 0 | d = 1 | (d = 1 ratio) / ln n |
|---|---|---|---|
| 10 | – | 1.344 ± 0.001 | 0.58 |
| 25 | 1.361 ± 0.002 | 1.707 ± 0.003 | 0.53 |
| 50 | 1.362 ± 0.004 | 2.087 ± 0.009 | 0.53 |
| 100 | 1.343 ± 0.014 | 2.568 ± 0.028 | 0.56 |
| 200 | 1.320 ± 0.028 | 3.08 ± 0.08 | 0.58 |
| 400 | – | 3.92 ± 0.25 | 0.65 |
| 800 | – | 5.8 ± 1.2 (chunks 3.6–9.4) | 0.87 |

Also: d = 2 gives 2.58 at n = 100 and 3.45 at n = 400; d = 5, n = 100 gives 2.22; d = 14, n = 200
gives 2.00. Errors are delta-method standard errors over all samples.

- The balanced ratio stays flat near 1.33–1.36, consistent with Lennon and Pittel's theorem. This
  is a sanity check of the method.
- With one extra worker the ratio grows steadily, roughly like 0.55 · ln n over n = 10 to 800. If
  the trend persisted, `second_moment_one_extra_worker`, and hence `second_moment`, would be false.
- The distribution of S has a heavy right tail. At n = 200, d = 1 the median is 7, the mean 12.5,
  the maximum 244, and 58% of E[S²] comes from samples with S ≥ 50 (`logs/mc_hist_200_201.txt`).
  Heavy tails make sample second moments tend to underestimate, but they also make the n = 400 and
  n = 800 estimates unreliable.
- A possible mechanism, not proved: in unbalanced markets most agents have a unique stable partner
  (Ashlagi, Kanoria and Leshno), so two stable matchings mostly coincide, and the penalty that no
  firm prefers the unmatched worker is strongly correlated between them. If the pair probability
  lost one factor of ln n less than the square of the single probability, the ratio would be
  Θ(ln n).

A disproof would need a rigorous asymptotic lower bound on Σ_{μ,ν} P(μ and ν both stable), which is
a Lennon–Pittel-type integral analysis and was not attempted.

## 7. Lean formalization

The Lean project in `lean/` depends on formal-conjectures at commit `9097e2f9` (Mathlib `v4.33.1`)
and uses its definitions unchanged.

- `PittelMoments/SmallCases.lean` (namespace `PittelSmall`): Lemma 1 as
  `numStableMatchings_eq_countB`, `expected_eq_sum`, `secondMoment_eq_sum`, `card_profile`;
  Proposition 2 as `expected_2_2`, `secondMoment_2_2`, `expected_2_3`, `secondMoment_2_3`. The
  sums use plain `decide`, with `maxRecDepth` raised for (2, 3).
- `PittelMoments/NTwo.lean` (namespace `PittelNTwo`): Theorem 3.

| Step | Lean |
|---|---|
| Step 1 | `isStableB_two_iff` |
| Step 2 | `mem_top_two`, `cand`, `cand_injective`, `countB_eq_sum_cand`, `valid_iff`, `forall_eq_zero_iff` |
| Step 3 | `arith_two`, `countB_two : countB p = if C p then 2 else 1`; upstream form `numStableMatchings_two`, `numStableMatchings_two_le` (for `p : Profile 2 (k+2)`) |
| Step 4 | `exists_perm_zero_one`, `F_eq`, `F_diag`, `F_mul`, `card_workers`, `profEquiv`, `card_firms`, `card_C`, `card_C_mul` |
| Moments | `sum_countB`, `sum_countB_sq`, `expected_two`, `secondMoment_two` |

The final statements:

```lean
theorem PittelNTwo.expected_two (m : ℕ) (hm : 2 ≤ m) :
    StableMarriage.Unbalanced.expectedNumStableMatchings 2 m = 1 + 1 / (4 * (m:ℝ) * ((m:ℝ) - 1))
theorem PittelNTwo.secondMoment_two (m : ℕ) (hm : 2 ≤ m) :
    StableMarriage.Unbalanced.secondMomentNumStableMatchings 2 m = 1 + 3 / (4 * (m:ℝ) * ((m:ℝ) - 1))
```

In `NTwo.lean`, `decide` is used only on `Fin 2` and `Perm (Fin 2)`. The two files each contain
their own copy of the bridge definitions, in separate namespaces. There is no `sorry`, no
`native_decide` and no added axiom; every theorem listed in `lean/Axioms.lean` depends on
`[propext, Classical.choice, Quot.sound]` (`logs/axioms.log`). An attempt to do (2, 4) by
`decide +kernel` (9216 profiles) succeeded for one of the two sums in about 9 minutes, but the file
with both was killed for lack of memory; it is not included (`logs/lean_2_4_attempt.txt`), and
Theorem 3 covers (2, 4) anyway.

## 8. Why the main question is out of reach

The targets are purely asymptotic: exact finite values say nothing about "eventually". Bounding
E[S²] requires uniform control of Σ_{μ,ν} P(μ and ν both stable), which by Pittel's method is a
4n-dimensional integral. In the balanced case Lennon and Pittel's analysis of it runs to about 50
pages. Going from two firms to three already makes the case analysis of Section 4 grow quickly,
and nothing in the structural argument extends to n → ∞. The Monte Carlo suggests that the
statement may in fact be false, in which case the needed result is an asymptotic lower bound of
the same difficulty.

## References

- B. Pittel, *On likely solutions of the stable matching problem with unequal numbers of men and
  women*, arXiv:1701.08900 (2017).
- C. Lennon, B. Pittel, *On the likely number of solutions for the stable marriage problem*,
  Combinatorics, Probability and Computing 18 (2009), 371–421.
- I. Ashlagi, Y. Kanoria, J. D. Leshno, *Unbalanced random matching markets: the stark effect of
  competition*, Journal of Political Economy 125 (2017), 69–98.
- B. Pittel, *The average number of stable matchings*, SIAM J. Discrete Math. 2 (1989), 530–549.
- D. Gusfield, R. W. Irving, *The Stable Marriage Problem: Structure and Algorithms*, MIT Press
  (1989).
- formal-conjectures,
  [`FormalConjectures/Arxiv/1701.08900/SecondMoment.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Arxiv/1701.08900/SecondMoment.lean).
