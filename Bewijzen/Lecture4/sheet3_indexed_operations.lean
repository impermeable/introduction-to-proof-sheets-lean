import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
import Bewijzen.Customlib.Sets

open WaterproofGenre
open Verbose.NameLess
open scoped Bewijzen.IntervalNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma emptySet
addAnonymousGoalSplittingLemma intervalMembership
addAnonymousGoalSplittingLemma intervalArithmetic
addAnonymousGoalSplittingLemma natArithmetic
addAnonymousGoalSplittingLemma singleInterval
addAnonymousGoalSplittingLemma archimedean
addAnonymousGoalSplittingLemma indexedIntervals

#doc (WaterproofGenre) "Indexed Operations" =>

```lean
-- Example 2.2.15
Example "2.2.15"
  Given:
  Assume:
  Conclusion: (⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)) = [0, 1]
Proof:
  Let's first prove that (⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)) ⊆ [0, 1]
  · Fix x
    Assume that x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
    Since x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
    we get that x ∈ [0, 1 + 1 / 1)
    Since x ∈ [0, 1 + 1 / 1)
    we get that 0 ≤ x and x < 1 + 1 / 1
    We discuss depending on whether x ≤ 1 or ¬ (x ≤ 1)
    · Assume that x ≤ 1
      It suffices to prove that 0 ≤ x ∧ x ≤ 1
      Let's first prove that 0 ≤ x
      · We conclude by hypothesis
      Let's now prove that x ≤ 1
      · We conclude by hypothesis
    · Assume that ¬ (x ≤ 1)
      Since ¬ (x ≤ 1) we get that x > 1
      Since x > 1 we get that x - 1 > 0
      Since x - 1 > 0
      we get that ∃ k : ℕ, k ≥ 1 ∧ k > 1 / (x - 1)
      Since ∃ k : ℕ, k ≥ 1 ∧ k > 1 / (x - 1)
      we get k : ℕ such that k ≥ 1 ∧ k > 1 / (x - 1)
      Since k ≥ 1 ∧ k > 1 / (x - 1)
      we get that k ≥ 1 and k > 1 / (x - 1)
      Since x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
      and k ≥ 1
      we get that x ∈ [0, 1 + 1 / k)
      Since x ∈ [0, 1 + 1 / k)
      we get that 0 ≤ x and x < 1 + 1 / k
      Since k > 1 / (x - 1) and x - 1 > 0
      we get that 1 / k < x - 1
      Let's prove it's contradictory
      Since x < 1 + 1 / k and 1 / k < x - 1 we conclude that False
  Let's now prove that [0, 1] ⊆
    ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
  · Fix x
    Assume that x ∈ [0, 1]
    Since x ∈ [0, 1] we get that 0 ≤ x and x ≤ 1
    It suffices to prove that
      ∀ n : ℕ, n ≥ 1 → x ∈ [0, 1 + 1 / n)
    Fix n
    Assume that n ≥ 1
    It suffices to prove that 0 ≤ x ∧ x < 1 + 1 / n
    Let's first prove that 0 ≤ x
    · We conclude by hypothesis
    Let's now prove that x < 1 + 1 / n
    · Since n ≥ 1 and x ≤ 1 we conclude that x < 1 + 1 / n
QED
```

::::multilean
```lean
-- Exercise 2.2.25
Exercise "2.2.25"
  Given:
  Assume:
  Conclusion: (⋃ (n : ℕ) (_ : n ≥ 1), [0, 1 - 1 / n]) is an interval
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

::::multilean
```lean
-- Exercise 2.2.26a
Exercise "2.2.26a"
  Given:
  Assume:
  Conclusion: (⋂ (n : ℕ), [n]) = (∅ : Set ℕ)
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
