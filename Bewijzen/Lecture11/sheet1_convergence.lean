import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Sequences

open WaterproofGenre
open Verbose.NameLess

-- ══════════════════════════════════════════════════════════════
-- Preamble
--
-- The mathematics lives in `Bewijzen.Customlib.Sequences`: the definition of
-- convergence, the reciprocal tail estimates that close each line of an estimate
-- chain, and the closed forms of `|u n - l|` for the sequences below.  All that
-- remains here is declaring the definitions unfoldable and registering the
-- lemmas this sheet quotes.
-- ══════════════════════════════════════════════════════════════

configureUnfoldableDefs converges_to IsConvergent

addAnonymousFactSplittingLemma archimedean_nat

addAnonymousComputeLemma abs_one_div_nat
addAnonymousComputeLemma abs_one_div_sq_nat
addAnonymousComputeLemma abs_one_div_two_pow
addAnonymousComputeLemma abs_sub_three_div_two
addAnonymousComputeLemma abs_sub_seven_div_two_cancel
addAnonymousComputeLemma abs_sub_one_div_two
addAnonymousComputeLemma abs_sub_one_combine
addAnonymousComputeLemma abs_neg_one_div_add_two

addAnonymousGoalSplittingLemma one_div_le_one_div_nat
addAnonymousGoalSplittingLemma one_div_sq_le_one_div_sq_nat
addAnonymousGoalSplittingLemma one_div_sq_le_one_div_nat
addAnonymousGoalSplittingLemma one_div_two_pow_le_two_pow_nat
addAnonymousGoalSplittingLemma one_div_two_pow_le_one_div_nat
addAnonymousGoalSplittingLemma one_div_add_two_le_one_div_nat
addAnonymousGoalSplittingLemma three_div_two_mul_le_three_div_four_mul
addAnonymousGoalSplittingLemma three_div_four_mul_le_three_div_four_mul
addAnonymousGoalSplittingLemma three_div_four_mul_lt
addAnonymousGoalSplittingLemma inv_lt_bridge

-- Feel free to remove the prose

#doc (WaterproofGenre) "Convergence" =>

# 9.2 Convergence

A sequence `u : ℕ → ℝ` *converges to* `l` when, for every `ε > 0`, the terms `u(n)`
eventually stay within `ε` of `l`:

  `u converges to l  :=  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u(n) - l| < ε`

and `u converges` means `u` has some limit.

## Proposition 9.2.16

Every proof on this sheet has the same opening moves: unpack `u converges` into
`∃ l : ℝ, u converges to l`, choose a candidate limit, fix an `ε > 0`, pick a
threshold `M`, announce that `M` works, restate what `M` still has to satisfy,
and fix an `n ≥ M`. What is left is an estimate of `|u(n) - l|`.

Restating the goal with `It suffices to prove that ∀ n ≥ M, |u(n) - l| < ε` is
never strictly necessary — Lean already knows what is left to prove — but writing
it down keeps the proof readable, exactly as you would do on paper.

Instead of a ceiling function we use that there is a natural number `M` above any
given real number, which we may take to be at least `1`:
`We obtain M : ℕ such that M ≥ 1 and M > 1 / ε`. Both are valid on paper; this
style fits Verbose better, and `M ≥ 1` is what makes dividing by `M` harmless.

The estimate itself is a `Calc` chain, one line per step, exactly as you would
write it on paper. A step is closed either `by computation` (algebra: substituting
the definition of the sequence and removing the absolute value signs) or `since`
the facts you would quote on paper for that step. Do not try to jump from
`|u(n) - l|` to `ε` in one go: each line of the chain should be a step you could
defend out loud, and if one of them is not, ask your teacher to check it.

```lean
noncomputable abbrev y : ℕ → ℝ := fun n => 1 / n

Example "9.2.16"
  Given:
  Assume:
  Conclusion: y converges
Proof:
  It suffices to prove that ∃ l : ℝ, y converges to l
  Let's prove that 0 works
  Fix ε > 0
  We obtain M : ℕ such that M ≥ 1 and M > 1 / ε
  Let's prove that M works
  It suffices to prove that ∀ n ≥ M, |y(n) - 0| < ε
  Fix n ≥ M
  Calc |y(n) - 0| = |1 / n - 0| by computation
    _ = |1 / n| by computation
    _ = 1 / n by computation
    _ ≤ 1 / M since M ≥ 1 and n ≥ M
    _ < ε since ε > 0 and M > 1 / ε
QED
```

## Exercise 9.2.20

```lean
noncomputable abbrev a : ℕ → ℝ := fun n => 1 / ((n : ℝ) * n)
```

::::multilean
```lean
Exercise "9.2.20"
  Given:
  Assume:
  Conclusion: a converges
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::

## Exercise 9.2.21

Here the limit is not `0`, so the absolute value hides a subtraction of fractions:
rewriting `|b(n) - 3 / 2|` as `3 / (2 * (2 * n + 1))` is the first step of the
chain. The threshold `M > 3 / (4 * ε)` is found by working backwards from the
last line of the chain — do that computation on scrap paper first, then write the
proof forwards.

```lean
noncomputable abbrev b : ℕ → ℝ := fun n => (3 * (n : ℝ)) / (2 * n + 1)
```

::::multilean
```lean
Exercise "9.2.21"
  Given:
  Assume:
  Conclusion: b converges
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::

## Exercise 9.2.22

Rewriting `|c(n) - 7 / 2|` takes two separate moves, so give each its own line:
first cancel the `3` against the `7 / 2`, then put what is left over one
denominator and drop the absolute value signs.

```lean
noncomputable abbrev c : ℕ → ℝ := fun n => 3 + ((n : ℝ) - 1) / (2 * n + 1)
```

::::multilean
```lean
Exercise "9.2.22"
  Given:
  Assume:
  Conclusion: c converges
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::

## Exercise 9.2.23

```lean
noncomputable abbrev d : ℕ → ℝ := fun n => 1 / (2 : ℝ) ^ n
```

::::multilean
```lean
Exercise "9.2.23"
  Given:
  Assume:
  Conclusion: d converges
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::

## Exercise 9.2.24

```lean
noncomputable abbrev z : ℕ → ℝ := fun n => ((n : ℝ) + 1) / (n + 2)
```

::::multilean
```lean
Exercise "9.2.24"
  Given:
  Assume:
  Conclusion: z converges
Proof:
```
:::input
```lean

```
:::
```lean
QED
```
::::
