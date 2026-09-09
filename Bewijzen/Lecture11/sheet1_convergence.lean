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

The biggest difference between Waterproof and paper proofs in this exercise sheet, is the way sequences are defined. They are defined as functions from the naturals to the reals, and the definition itself can be found all the way at the end of the line: `1 / n` for the first example.

We also want to start by unpacking the definition of converges with `It suffices to prove that ...`

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
  We obtain M ∈ ℕ such that M ≥ 1 and M > 1 / ε
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
Next we have 4 convergence exercises.



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
