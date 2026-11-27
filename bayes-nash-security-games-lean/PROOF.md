# Bayes–Nash equilibria in security games: a Lean audit and special cases

*Draft, November 2026. Written with AI assistance (Claude) and not checked by a human expert; see
[CHECKS.md](CHECKS.md) for how it has been checked so far. Every theorem in Sections 3–5 is also
proved in Lean 4 (Section 7).*

**This document does not solve the open problem.** It concerns the Lean formalization of the
problem: whether it says what the paper asks (Section 2), what its equilibrium predicate means
(Section 3), and two easy special cases and an example (Sections 4–5). Section 8 explains why the
problem itself is out of reach of these methods.

## 1. The problem

V. Conitzer [Co26] considers *Bayesian simple security games*. There is a finite set T of n
targets, a number r ≤ n of defender resources, and a finite set Θ of attacker types with a prior
p on Θ. The defender has payoffs u⁰_t ≤ u¹_t at target t when it is attacked while uncovered
(u⁰) or covered (u¹); a type-θ attacker has payoffs v⁰_θt ≥ v¹_θt. The defender chooses r of the
targets (a mixed strategy is a distribution over r-subsets); the attacker learns θ and chooses
one target. Conitzer asks whether a Bayes–Nash equilibrium can be computed in polynomial time.
The paper notes that computing a Stackelberg (commitment) strategy in this model is NP-hard, that
the non-Bayesian variant in which the attacker has several resources is solvable in polynomial
time [KCP11], and that an algorithm which seems fast in practice exists but has no proved
polynomial bound. The question was first posed in 2015.

In formal-conjectures [FC] this is the statement

```lean
theorem exists_isPolyTime_bayesNash :
    ∃ solve : GameInput → EquilibriumOutput,
      IsPolyTime solve ∧ ∀ (g : GameInput), g.Valid → g.IsBayesNash (solve g)
```

where `GameInput = ℕ × List (ℚ × ℚ) × List (ℚ × List (ℚ × ℚ))` holds r, the defender's table
(u⁰_t, u¹_t), and for each type its prior and its table (v⁰_θt, v¹_θt), and
`EquilibriumOutput = List ℚ × List (List ℚ)` holds coverage marginals c_t and, for each type, a
distribution a_θ over targets.

**Notation.** For a valid game g, coverage c ∈ ℚᵀ and attack profile a = (a_θ)_θ, put

- F_r = { c ∈ ℚᵀ : 0 ≤ c_t ≤ 1 for all t, Σ_t c_t = r } (feasible coverage marginals);
- U_θ(c, t) = (1 − c_t) v⁰_θt + c_t v¹_θt (the attacker's expected utility, Lean `attU`);
- gain_t(a) = (Σ_θ p_θ a_θt)(u¹_t − u⁰_t) (the defender's marginal gain from covering t,
  Lean `gain`);
- D(a, c′) = Σ_θ p_θ Σ_t a_θt ((1 − c′_t) u⁰_t + c′_t u¹_t) (the defender's expected utility,
  Lean `defU`).

`IsBayesNash g e` says, writing c_t and a_θt for the entries of e (read with default 0 beyond
the end of a list): e has n coverage entries and one row of length n per type; c ∈ F_r; each
a_θ is a probability vector; a_θt > 0 implies U_θ(c, s) ≤ U_θ(c, t) for all s; and

  for all t, s: c_t > 0 and c_s < 1 imply gain_s(a) ≤ gain_t(a).   (P)

Condition (P) is a pairwise "no profitable shift of coverage" test, not literally the statement
that c is a best response. Section 3 shows that it is equivalent to it.

## 2. Faithfulness of the formalization

We read the paper and the formal statement side by side. We found no mistranslation.

**Polynomial time and encoding.** `IsPolyTime` is Mathlib's `TM2ComputableInPolyTime`: a finite
multi-stack Turing machine (finite stack indices, alphabets, labels and states) that maps the
encoding of the input to exactly the encoding of the output within p(|input|) steps for a
polynomial p, on every input, including invalid games. The remaining requirements (other stacks
empty and state reset at halting) are harmless technicalities. Natural numbers are encoded in
binary, integers as pairs of naturals, rationals as reduced (numerator, denominator) pairs, and
pairs and lists in self-delimiting blocks with a constant-factor blowup. The input size is
therefore the usual bit length of the explicitly listed payoff tables and priors, plus the bits of
r, which is at most n. This matches the explicit input model of the paper.

**Output size.** A polynomial-time solver must print an equilibrium of polynomial bit length.
Such equilibria exist: a BNE of this two-player Bayesian game is a solution of a linear
complementarity problem of polynomial size, which has a rational basic solution of polynomial bit
length. So the output requirement does not make the problem harder than in the paper.

**Validity.** `Valid` requires 0 < n (an addition, harmless), r ≤ n, a prior that is nonnegative
and sums to 1, complete tables, u⁰_t ≤ u¹_t and v¹_θt ≤ v⁰_θt. This is the paper's model, with
the same orientation (uncovered, covered).

**Marginals instead of mixtures.** The defender's mixed strategy is represented by its coverage
marginals c ∈ F_r instead of a distribution over r-subsets. All expected utilities depend on the
mixed strategy only through c. Since there are no scheduling constraints, every c ∈ F_r is the
marginal vector of some distribution over r-subsets, and one with support of size at most n + 1
can be found in polynomial time (comb sampling). So the marginal model is faithful. This standard
fact is stated upstream and is not proved in Lean here.

**The equilibrium predicate.** The attacker clause is the usual best-response condition for each
type. The defender clause (P) is equivalent to c maximizing D(a, ·) over F_r (Theorem 3 below,
proved in Lean). So `IsBayesNash` is exactly a Bayes–Nash equilibrium in marginal form. Two minor
deviations:

1. The attacker clause is imposed also for types with prior 0 (an interim BNE). This is a
   refinement, not a weakening, and it never destroys existence, because the strategies of
   zero-prior types do not affect the defender. It does break interchangeability of equilibria in
   degenerate games (seen in the enumeration, Section 6).
2. Entries are read with `getD` (default values beyond the end of a list). The length clauses of
   `IsBayesNash` rule out junk entries; Theorem 4 makes this precise.

**Non-vacuity.** Valid games exist (for example g₀ in Section 5, proved valid in Lean), and the
conclusion is neither trivially true nor trivially false.

**Verdict.** The statement is a faithful formalization of Conitzer's question.

## 3. `IsBayesNash` is the standard equilibrium condition

**Theorem 1 (`pairwise_iff_optimal`).** Let c ∈ F_r and g ∈ ℚᵀ. Then

  (for all t, s: c_t > 0 and c_s < 1 imply g_s ≤ g_t)  ⟺  Σ_t g_t c′_t ≤ Σ_t g_t c_t for all c′ ∈ F_r.

*Proof.* (⇒) Let S = { t : c_t > 0 }. If S is nonempty, put λ = min_{s ∈ S} g_s; otherwise put
λ = Σ_t |g_t|. Let c′ ∈ F_r. If c′_t > c_t then c_t < 1, so g_t ≤ g_s for every s ∈ S by the
hypothesis, and g_t ≤ λ (trivially so if S is empty). If c′_t < c_t then c_t > 0, so t ∈ S and
λ ≤ g_t. In all cases (g_t − λ)(c′_t − c_t) ≤ 0. Summing over t and using Σ c′_t = Σ c_t = r,

  Σ_t g_t c′_t − Σ_t g_t c_t = Σ_t (g_t − λ)(c′_t − c_t) ≤ 0.

(⇐) Suppose c_t > 0, c_s < 1 and g_s > g_t; then t ≠ s. Put ε = min(c_t, 1 − c_s) > 0 and move ε
of coverage from t to s. The result c′ lies in F_r and Σ g c′ = Σ g c + ε(g_s − g_t) > Σ g c, a
contradiction. ∎

**Lemma 2 (`defU_eq`).** D(a, c′) = D(a, 0) + Σ_t gain_t(a) c′_t.

*Proof.* Expand (1 − c′_t)u⁰_t + c′_t u¹_t = u⁰_t + c′_t (u¹_t − u⁰_t) and exchange the sums over
θ and t. ∎

So the defender's utility is affine in c′, with gradient (gain_t(a))_t.

For c ∈ ℚᵀ and a, write `mkOutput g c a` for the output whose coverage list is (c_t)_t and whose
rows are (a_θt)_t.

**Theorem 3 (`isBayesNash_mkOutput_iff_optimal`).** `IsBayesNash g (mkOutput g c a)` holds if
and only if

- c ∈ F_r,
- each a_θ is a probability vector,
- a_θt > 0 implies U_θ(c, s) ≤ U_θ(c, t) for all s, and
- D(a, c′) ≤ D(a, c) for every c′ ∈ F_r.

*Proof.* For outputs of the form `mkOutput g c a` the length clauses hold and the entries read
with `getD` are exactly c_t and a_θt, so `IsBayesNash` reduces to the first three conditions and
(P) for g = gain(a) (`isBayesNash_mkOutput_iff`). By Lemma 2, D(a, c′) ≤ D(a, c) is equivalent to
Σ gain_t(a) c′_t ≤ Σ gain_t(a) c_t, and Theorem 1 finishes the proof. ∎

**Theorem 4 (`eq_mkOutput_of_isBayesNash`, `isBayesNash_iff_optimal`).** If `IsBayesNash g e`,
then e = `mkOutput g c a` with c_t and a_θt the entries of e. Consequently, for every output e,
`IsBayesNash g e` holds if and only if e = `mkOutput g c a` for some c and a satisfying the four
conditions of Theorem 3.

*Proof.* The length clauses say that e has exactly n coverage entries and exactly one row of
length n per type, so e is determined by the entries read with `getD`, which are c and a. The
second statement follows from the first and Theorem 3. ∎

Theorem 4 is what makes the faithfulness claim of Section 2 precise: `IsBayesNash` holds exactly
for the encodings of interim Bayes–Nash equilibria in marginal form. (Before the audit only
Theorem 3 was proved; see CHECKS.md.)

## 4. The cases r = 0 and r = n

**Theorem 5 (`exists_isBayesNash_of_zero`, `exists_isBayesNash_of_full`).** For every valid game
with r = 0, and for every valid game with r = n, there is an output e with `IsBayesNash g e`.

*Proof.* If r = 0, then F_r = {0}; take c = 0. If r = n, then F_r = {(1, …, 1)}; take c = 1. For
each type θ, the finite nonempty set of targets (n > 0 by validity) contains a target b_θ
maximizing U_θ(c, ·); let a_θ be the point mass at b_θ. The attacker clauses hold by
construction. Condition (P) holds vacuously: for r = 0 no t has c_t > 0, and for r = n no s has
c_s < 1. ∎

These cases are trivial. The defender has no choice, and the result has no strategic content. It
is the correctness half only; nothing about `IsPolyTime` is proved, even in these cases (though a
polynomial-time algorithm for them is obvious).

## 5. A concrete instance with non-unique equilibrium coverage

Let g₀ have r = 1, two targets 0 and 1, defender payoffs (u⁰, u¹) = (−3, 2) at target 0 and
(−5, 0) at target 1, and two types, each with prior 1/2, with payoff tables

- type A: (v⁰, v¹) = (0, −4) at target 0 and (4, −4) at target 1;
- type B: (v⁰, v¹) = (4, −1) at target 0 and (0, −3) at target 1.

**Theorem 6 (`g₀_valid`, `instance_isBayesNash_family`, `instance_isBayesNash`).** g₀ is valid,
and for every rational x with 1/3 ≤ x ≤ 7/8, coverage c = (x, 1 − x) together with type A
attacking target 1 and type B attacking target 0 is a Bayes–Nash equilibrium. In particular
x = 1/3, c = (1/3, 2/3) is one.

*Proof.* Validity is a direct check. Type A gets U_A(c, 0) = −4x and U_A(c, 1) = 4x − 4(1 − x) =
8x − 4, so target 1 is a best response iff x ≥ 1/3. Type B gets U_B(c, 0) = 4(1 − x) − x = 4 − 5x
and U_B(c, 1) = −3(1 − x), so target 0 is a best response iff 4 − 5x ≥ 3x − 3, i.e. x ≤ 7/8. For the defender, gain_0 = (1/2)(2 − (−3)) = 5/2 and
gain_1 = (1/2)(0 − (−5)) = 5/2. The gains are equal, so (P) holds for every c. ∎

The equilibrium coverage is not unique, but only because of the exact tie gain_0 = gain_1, so g₀
is not a generic game. The enumeration (Section 6) found non-unique coverage also in some generic
games, where the defender is indifferent between targets that no type attacks.

## 6. Computer checks

These checks are evidence, not part of any proof. `scripts/bne_enum.py` uses only the Python
standard library and exact `Fraction` arithmetic. For each game it guesses, for every target,
whether c_t = 0, 0 < c_t < 1 or c_t = 1, and a support for every type; it solves the resulting
indifference equations exactly; and it keeps a candidate only if it passes `check_bne`, a literal
transcription of `IsBayesNash`. It is not guaranteed to list all equilibria, only to certify the
ones it finds. Games have n ≤ 4 targets, at most 3 types (at most 2 when n = 4), and r uniform in
{0, …, n}.

**Table 1. Enumeration runs.**

| Command (log) | Games | Found a BNE | Distinct equilibrium coverages | Interchangeability fails |
|---|---|---|---|---|
| `bne_enum.py 0 200 5` (`logs/bne_enum_seed0.log`): payoffs in {−5, …, 5}, zero priors allowed | 200 | 200 | 36 | 12 |
| `bne_enum.py 1 150 1000` (`logs/bne_enum_generic_seed1.log`): payoffs in {−1000, …, 1000}, positive priors | 150 | 150 | 8 | 0 |

"Interchangeability fails" means that the coverage of one found equilibrium combined with the
attacks of another is not an equilibrium. This happened only in the small-integer games, which
have ties or zero priors. Since BNE exist in every finite Bayesian game (Nash), finding one in
every game checks the formal definitions, not the open question. The game g₀ of Section 5 comes
from the first run (with a zero-prior type removed). Timings are in `logs/timing.log`.

## 7. Lean formalization

The directory `lean/` is a Lean 4 (v4.33.1) project depending on formal-conjectures at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53` (which depends on Mathlib `v4.33.1`). It imports the
upstream module `FormalConjectures.Arxiv.«2610.08796».BayesianSecurityGames` and uses its
definitions unmodified.

- `BayesNashSecurityGames/DefenderBR.lean`: `Feasible`, `mkOutput`, `attU`, `gain`, `defU`;
  `pairwise_iff_optimal` (Theorem 1), `defU_eq` (Lemma 2), `isBayesNash_mkOutput_iff` and
  `isBayesNash_mkOutput_iff_optimal` (Theorem 3), `eq_mkOutput_of_isBayesNash` and
  `isBayesNash_iff_optimal` (Theorem 4), `exists_isBayesNash_of_zero` and
  `exists_isBayesNash_of_full` (Theorem 5).
- `BayesNashSecurityGames/Instance.lean`: `g₀`, `g₀_valid`, `instance_isBayesNash_family`,
  `instance_isBayesNash` (Theorem 6).

All declarations are in the namespace `OMA.BNSG`. There is no `sorry`, `native_decide` or added
axiom; `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each theorem listed in
`lean/Axioms.lean` (`logs/axioms.log`; build output in `logs/lean_build.log`). The shape lemma
`eq_mkOutput_of_isBayesNash` is adapted from the auditor's scratch proof, kept in
`logs/reviewer_All.lean.txt`.

## 8. Why the main question is out of reach

The open statement asks for a polynomial-time algorithm, verified in Lean, that outputs an
equilibrium for every game.

- **Proving it** would need an algorithm that is known to run in polynomial time. None is known.
  The paper mentions a complicated algorithm that seems fast in practice, but nobody has proved a
  polynomial bound for it. Even with such an algorithm, the Lean proof would have to build a
  concrete `TM2` machine for it, including exact rational arithmetic, and verify its running
  time. Mathlib currently has little infrastructure for this (for example, no general lemma that
  polynomial-time `TM2` computations compose), so this would be a large project on its own.
- **Disproving it** is out of reach for a different reason. Finding a BNE here is a total search
  problem in PPAD (it reduces to a linear complementarity problem solvable by Lemke's algorithm).
  If P = NP, every such problem is solvable in polynomial time. So a proof that no polynomial-time
  algorithm exists would prove P ≠ NP.
- **Special cases.** With one attacker type, the defender's Nash strategies are her minimax
  strategies in a zero-sum game [KYKCT11], which can be computed in polynomial time by linear
  programming or by the ORIGAMI water-filling algorithm [KJTPOT09]. Formalizing even the existence
  half of this over ℚ (a rational water-level argument with degenerate cases) was estimated at
  several hundred Lean lines and was not attempted, since existence alone is classical and does
  not touch the complexity question.

The results of Sections 3–5 therefore do not bring the open problem closer. Their value is that
they confirm that the formal statement asks the right question.

## References

- [Co26] V. Conitzer, *Open problem: Computing Bayes–Nash equilibrium in simple security games*,
  arXiv:2610.08796 (2026), https://arxiv.org/abs/2610.08796.
- [FC] formal-conjectures, `FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean`,
  https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Arxiv/2610.08796/BayesianSecurityGames.lean.
- [KJTPOT09] C. Kiekintveld, M. Jain, J. Tsai, J. Pita, F. Ordóñez and M. Tambe, Computing optimal
  randomized resource allocations for massive security games, *AAMAS* 2009.
- [KYKCT11] D. Korzhyk, Z. Yin, C. Kiekintveld, V. Conitzer and M. Tambe, Stackelberg vs. Nash in
  security games: an extended investigation of interchangeability, equivalence, and uniqueness,
  *J. Artificial Intelligence Res.* 41 (2011), 297–327.
- [KCP11] D. Korzhyk, V. Conitzer and R. Parr, Security games with multiple attacker resources,
  *IJCAI* 2011.
