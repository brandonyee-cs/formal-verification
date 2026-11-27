# The Catch-Up conjecture: what is proved, and how

This document states precisely what the Lean files prove and gives the paper proofs behind them:
the parity lemma, the direct evaluator, the certificate method and the soundness of its checker,
and the solvers. **It does not prove the conjecture.** The conjecture is about every N; the Lean
results cover N ≤ 16 (plus the parity fact for every N), and the computations cover N ≤ 39.

## 1. The problem

Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) is played on a finite set S of positive integers.
Both scores start at 0. Player 1 first removes exactly one number, which is added to their score.
After that the players alternate turns. On a turn the current player removes numbers one at a
time, adding each to their score, and must stop as soon as their score is at least the
opponent's; before the last pick of the turn they are strictly behind. If even taking every
remaining number would leave the player behind, they take everything and the game ends. When S is
empty, the higher score wins and equal scores draw.

Write T_N = 1 + 2 + ... + N = N(N+1)/2. The paper solved the game on {1, ..., n} for n ≤ 20 and
conjectured that it is a draw exactly when T_N is even (N ≡ 0 or 3 mod 4).

The formal-conjectures file `FormalConjectures/Paper/CatchUpConjecture.lean` (commit `9097e2f9`)
defines `Outcome = win | loss | draw`, `Outcome.neg` (swap win and loss), `Outcome.best` (a fold
that returns win if some entry is win, otherwise draw if some entry is draw, otherwise loss), and

```lean
noncomputable def valueAux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) : Outcome
noncomputable def value (S : Finset ℕ) : Outcome := valueAux S 0 0 true

theorem value_of_even_mul_succ_self_div_two
    (N : ℕ) (h_even : Even (N * (N + 1) / 2)) :
    value (.Icc 1 N) = .draw
```

`valueAux R a b f` is the value for the player about to pick, with score a, against score b:

- if R = ∅: win if a > b, loss if a < b, draw if a = b;
- else if a + ΣR < b: loss;
- else the best, over x ∈ R, of the child value
  - (valueAux (R∖{x}) b (a+x) false).neg if f (first move: the turn always passes),
  - (valueAux (R∖{x}) b (a+x) false).neg if a + x ≥ b (caught up: the turn passes),
  - valueAux (R∖{x}) (a+x) b false otherwise (still behind: the same player picks again).

## 2. Faithfulness of the formalization

The model was compared with the rules as stated in the paper and in the Plus Magazine summary.

- On a tied score at the start of a turn, one pick puts the player level or ahead, so the turn
  ends after one pick. `valueAux` does the same, since a + x ≥ b holds at once.
- The "cannot catch up" branch is right: a player who stays behind after taking everything ends
  the game behind, and loses.
- The paper also has a secondary preference (lose by as little as possible). It does not change
  the win/draw/loss class, which is all that `value` records.
- `Even (N * (N + 1) / 2)` is exactly "T_N is even", because N(N+1) is always even. N = 0 is
  the trivial case `value ∅ = draw`.
- The solver in `scripts/solver2.cpp`, which follows `valueAux`, reproduces every value in the
  paper's table for n = 1..20: player 1 wins at n = 2, 5, 6, 13, 17 (and n = 1), player 2 wins
  at n = 9, 10, 14, 18, and the game is a draw at n = 3, 4, 7, 8, 11, 12, 15, 16, 19, 20.

No mistranslation was found.

## 3. The parity lemma (all N)

**Lemma (`CatchUpOMA.valueAux_draw_even`).** If `valueAux R a b f = draw`, then a + b + ΣR is
even.

*Proof.* Induction on |R|. If R = ∅, the value is draw only when a = b, and 2a is even. Otherwise
the value is not given by the loss branch (that would be loss), so it is `best` of the children.
By `best_eq`, `best os = draw` implies `draw ∈ os`, so some child x has value draw. Since
`neg` fixes only draw, the child position itself — (R∖{x}, b, a+x) or (R∖{x}, a+x, b) — has value
draw. In both cases the total score plus remaining sum is b + (a+x) + Σ(R∖{x}) = a + b + ΣR. By
the induction hypothesis this is even. ∎

**Theorem (`CatchUpOMA.value_ne_draw_of_odd`).** For every N, if T_N is odd then
`value (Icc 1 N) ≠ draw`.

*Proof.* Apply the lemma with a = b = 0 and R = {1, ..., N}, and use Σ_{x=1}^{N} x = N(N+1)/2
(`sum_Icc_id`). ∎

So the conjecture is equivalent to "the game on {1, ..., N} is a draw if and only if T_N is
even". The file records this as `conj_iff`, but `conj_iff` takes the conjecture as a hypothesis:
it is a trivial corollary and makes no progress on the conjecture. The parity lemma is the easy,
complementary direction.

## 4. The direct evaluator (N ≤ 12)

`valueAux` is noncomputable (it recurses over `Finset`s by well-founded recursion), so the kernel
cannot evaluate it directly. `CatchUpLean/Eval.lean` gives a computable replacement.

- `ev n l a b f` is the same recursion on a list `l`, structurally recursive on a fuel argument
  n, with `Outcome.best` over `l.map`.
- **`valueAux_eq_ev`.** If l has no duplicates and length ≤ n, then
  `valueAux l.toFinset a b f = ev n l a b f`. The proof is by induction on n. The only subtle
  point is that `valueAux` maps over `Finset.toList`, whose order is unspecified. This is handled
  by `best_eq` (the value of `best` depends only on which outcomes occur), which gives
  `best_congr`: two lists with the same members have the same `best`.
- `ge n w l a b f` is a short-circuiting threshold evaluator: **`ge_true_iff`** says
  `ge n true ... = true ↔ ev ... = win` and `ge n false ... = true ↔ ev ... ≠ loss`.
- **`value_eq_draw_of`.** If `ge N false (range' 1 N) 0 0 true = true` and
  `ge N true (range' 1 N) 0 0 true = false`, then `value (Icc 1 N) = draw` (the value is neither
  loss nor win).
- **`conj_le_12`.** The upstream statement for N ≤ 12: the cases N = 0, 3, 4, 7, 8, 11, 12 are
  closed by `decide +kernel` on the two Boolean conditions, and the other N have odd T_N, which
  contradicts the hypothesis.

The kernel explores the whole game tree without memoization. With ascending move order the tree
for N = 12 has about 45 000 nodes; for N = 15 and 16 it has 1.45 M and 4.9 M
(`logs/thresh_15_16.log`), and a kernel run for N = 15 ran out of memory
(`logs/lean_N15_oom_exit137.log`). This is why the certificate method below was built.

## 5. The certificate method (N ≤ 16)

`CatchUpLean/Cert.lean` consists of a checker library (the first part of the file, also kept as
`lean/CertLib.lean.part`) followed by generated certificates.

### 5.1 The deficit evaluator

After the first move, the player to move is never ahead: when the turn passes, the new mover has
score b and the opponent a + x ≥ b; when the turn continues, the mover is still behind. Only the
deficit g = b − a matters. Define, with fuel n,

    D n [] g        = draw if g = 0, loss otherwise
    D n l g         = loss                    if Σl < g
    D n l g         = best over x ∈ l of  (D (n−1) (l∖x) (x − g)).neg   if g ≤ x   (turn passes)
                                         D (n−1) (l∖x) (g − x)          if x < g   (same player)

(and `D 0 l g = loss` for nonempty l, which never occurs with enough fuel).

**`valueAux_eq_D`.** If l has no duplicates, length ≤ n, a ≤ b, and (f → a = b), then
`valueAux l.toFinset a b f = D n l (b − a)`.

*Proof.* Induction on n, as for `ev`. At the first move a = b, so g = 0 and every x satisfies
g ≤ x; the first-move branch and the "caught up" branch coincide. The child positions satisfy the
hypotheses again (the new mover is behind by x − g or g − x). The `Finset.toList` order is again
handled by `best_congr`. ∎

In particular **`value_eq_D`**: `value (Icc 1 N) = D N (range' 1 N) 0`.

### 5.2 Claims and the checker

Let `thr true o` mean o = win and `thr false o` mean o ≠ loss. A position (l, g, w), with l an
ascending sublist of 1..N, is encoded as the natural number

    enc l g w = (Σ_{x ∈ l} 2^x · 1024 + g) · 2 + [w].

A **claim** is a pair (k, v) of a key and a Boolean, stored in a binary tree `Tr`. Its meaning
is `Sem l g w v :  thr w (D |l| l g) = v`, where (l, g, w) is the position with key k.

- `dec N k` decodes a key: l is the list of x ∈ 1..N whose bit is set in k / 2048, g = (k/2) mod
  1024, w = k mod 2.
- `look N T l g w` returns `T.find (enc l g w)` **only if** `dec N (enc l g w) = (l, g, w)`, and
  `none` otherwise. So a key that does not round-trip (for example g ≥ 1024, or a number outside
  1..N) can never be used.
- `child` looks up the claim for the child after picking x, and translates it: if g ≤ x the turn
  passes, the child is (l∖x, x − g, ¬w), and its stored Boolean is negated (because
  `thr w o.neg = ¬ thr (¬w) o`, lemma `thr_neg`); otherwise the child is (l∖x, g − x, w).
- `checkState N T l g w v` is the local check:
  - if l = []: v must equal `thr w (draw if g = 0 else loss)`;
  - if Σl < g: v must be false (the value is loss, and `thr w loss` is false for both w);
  - if v = true: **some** x ∈ l must have a child claim that is found and equals true;
  - if v = false: **every** x ∈ l must have a child claim that is found and equals false.
- `checkNode N T k v` runs `checkState` on the decoded position of k.

### 5.3 Soundness

**Theorem (`check_sound`).** If every node (k, v) of T satisfies `checkNode N T k v`, then for
all l, g, w, v: `look N T l g w = some v` implies `thr w (D |l| l g) = v`.

*Proof.* First, `Tr.find_sound`: if every node satisfies a predicate p and `T.find q = some v`,
then p q v holds, since `find` only ever returns a value stored at key q. (This does not use the
search-tree ordering; a badly ordered tree can only make lookups fail.) So a successful lookup
gives a claim that passed `checkState` at a position that decodes to (l, g, w).

Now induct on the length of l. If l = [], `checkState` fixed v to the true value. Otherwise, if
Σl < g, v = false and D = loss. Otherwise D is `best` of the children, and by `thr_best`,
`thr w (best os) = os.any (thr w)`. Every child list has length |l| − 1, so by the induction
hypothesis every child claim that `child` finds is semantically correct, and after the `thr_neg`
translation it gives the correct value of `thr w` on that child's outcome. If v = true, the
checker found a child with value true, so the `any` is true. If v = false, every child was found
with value false, so the `any` is false. In both cases `thr w (D |l| l g) = v`. ∎

Only claims that are actually stored and checked are trusted; a missing child makes a check
fail, never pass.

**Theorem (`value_eq_draw_of_cert`).** If T passes the check and contains the two root claims
`look N T (range' 1 N) 0 false = some true` and `look N T (range' 1 N) 0 true = some false`, then
`value (Icc 1 N) = draw`.

*Proof.* By `check_sound`, D N (range' 1 N) 0 is not loss and not win; by `value_eq_D` it is the
value. ∎

### 5.4 The certificates and the kernel check

`scripts/cert.cpp` computes the threshold values with a memoized search and collects claims
starting from the two roots: for a claim with v = true it includes the first child (in ascending
order of x) that witnesses it, and for v = false it includes all children. The claims are
reachable positions only, and each position appears once, so the certificate is a DAG folded
into a table, much smaller than the game tree: 799 claims for N = 12, 2818 for N = 15 and 4418
for N = 16.

`scripts/gen_cert_lean.py` sorts the claims by key and writes them as a balanced search tree. To
bound kernel memory, the tree is split into subtrees of at most 300 claims (`c16_0`, `c16_1`,
...) joined by separator claims. Each subtree's check `Tr.all (checkNode 16 cert16) c16_j = true`
and each separator's check is a separate theorem proved by `decide +kernel`, and
`Tr.all_node_intro` assembles them into `all16 : Tr.all (checkNode 16 cert16) cert16 = true`. The
root lookups are also `decide +kernel`. Then `value_Icc_16` follows from `value_eq_draw_of_cert`.

**`conj_le_16`.** The upstream statement for N ≤ 16: N = 0, 3, 4, 7, 8, 11, 12, 15, 16 by their
certificates, and the remaining N have odd T_N.

Nothing about `cert.cpp` or the generator needs to be trusted: if they produced a wrong or
incomplete certificate, the kernel check would fail. An auditor confirmed this on N = 7 by
flipping each of 9 leaf claims and each root claim (CHECKS.md).

### 5.5 Limits

Kernel memory grows across declarations in one file. `Cert.lean` (N ≤ 16) peaks at about
13 GB, of which about 7 GB are the Mathlib imports. A single file for N ≤ 20 (22 992 claims for
N = 20) passed 16 GB after 26 minutes and was stopped (`logs/lean_cert_le20.log`); a file for
N = 19 alone reached 10 GB after 6 minutes and was stopped because the machine was low on memory
(`logs/lean_cert_19.log.meta`). Larger N would need the certificates split across separately
compiled modules.

## 6. The solvers (N ≤ 39)

All solvers use the deficit form of Section 5.1: a state is (mask of remaining numbers, g), and
the first move is "P1 picks x, then P2 is behind by x".

- `scripts/solver2.cpp`: exact minimax with values in {−1, 0, 1}, memoized in an open-addressing
  hash table with full keys (mask·1024 + g), trying large numbers first and stopping at the
  first win. Values for every N ≤ 25 (`logs/solver2_0_26.log`).
- `scripts/solver3.cpp`: two threshold searches, "value ≠ loss" and "value = win", with a lossy
  fixed-size cache. Each cache entry stores the full key, and a collision only overwrites an
  entry, so the cache affects speed, never results. The key packing is valid for N ≤ 52 (g never
  exceeds N). The value is draw exactly when player 1 has a first move after which player 2
  cannot win, and no first move after which player 2 must lose. Logs:
  `logs/solver3_22_34.log`, `logs/solver3_even_31_52.log` (stopped after N = 39).
- `scripts/solver.cpp`: the first version of solver2, with a standard hash map.

Results:

| N | value | | N | value | | N | value |
|---|---|---|---|---|---|---|---|
| 1, 2 | P1 wins | | 13 | P1 wins | | 21, 22 | P1 wins |
| 3, 4 | draw | | 14 | P2 wins | | 23, 24 | draw |
| 5, 6 | P1 wins | | 15, 16 | draw | | 25, 26 | P1 wins |
| 7, 8 | draw | | 17 | P1 wins | | 27, 28 | draw |
| 9, 10 | P2 wins | | 18 | P2 wins | | 29, 30 | P1 wins |
| 11, 12 | draw | | 19, 20 | draw | | 31, 32, 35, 36, 39 | draw |

N ≤ 20 matches the paper; N = 21–25 are new and agree between solver2 and solver3; N = 26–30 come
from solver3 only. For N = 31–39 only the even-total cases were run. The conjecture holds for
every N ≤ 39 with T_N even, and every odd-total N ≤ 30 gives a win for one side, as the parity
lemma requires.

These are computations, not formal proofs. The independent solver in `independent-checks/cu.py`
(Section 7) agrees for N ≤ 12.

## 7. Other experiments

- `scripts/interval_table.py` prints V({1..k}, g) for a mover behind by g. The pattern is mostly
  "draw when g ≡ T_k (mod 2), win otherwise" for small g, win in a middle range and draw at
  g = T_k, but there are irregular exceptions (for example k = 12, g = 16..18). No closed form was
  found, so there is no obvious invariant for an induction on N.
- `scripts/rules.py` and `scripts/rulestrat.py` test simple memoryless strategies (take the
  largest, the smallest, the smallest catch-up number, an exact tie, and so on). None secures a
  draw for either player once N ≥ 7, so no explicit-strategy proof suggested itself.
- `scripts/thresh.py`, `scripts/treesize.py` and `scripts/treecount.cpp` count nodes of the
  unmemoized evaluators under different move orders; ascending order gave the smallest trees, about
  100 times smaller than descending order.
- The winner for odd T_N (W W W W L L W L W L W W for N = 1, 2, 5, 6, 9, 10, 13, 14, 17, 18, 21, 22)
  shows no simple pairing or strategy-stealing pattern.

## 8. References

- A. Isaksen, M. Ismail, S. J. Brams, A. Nealen, *Catch-Up: A Game in Which the Lead Alternates*,
  Game & Puzzle Design 1(2) (2015), 38–49; MPRA Paper No. 108784.
- S. J. Brams, *Game stymies AI*, Plus Magazine, https://plus.maths.org/game-stymies-ai.
- formal-conjectures, `FormalConjectures/Paper/CatchUpConjecture.lean`, commit
  `9097e2f90e66d2f6244209cb1c07f7120d17ec53`.
