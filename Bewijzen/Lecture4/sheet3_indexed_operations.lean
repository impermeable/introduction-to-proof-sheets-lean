import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
import Bewijzen.Customlib.Sets

open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
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
addAnonymousGoalSplittingLemma trichtomyContradictions

#doc (WaterproofGenre) "Indexed Operations" =>

Below is an example of indexed operations. These use the notations
`⋂ (n : ℕ) (_ : n ≥ 1), ...` and `⋃ (n : ℕ) (_ : n ≥ 1), ...` for intersections and
unions indexed by natural numbers starting from one. 
Notation `(n : ℕ)` specifies that we index by natural numbers — the default is indexing by reals.
Notation `(_ : n ≥ 1)` means that we consider only natural numbers
starting from one (0 is a natural number as well in Waterproof).
Note that here we use the big versions of the
regular union and intersection - `\Inter` for `⋂` and `\Union` for `⋃`.

```lean
-- Example 2.2.19
Example "2.2.19"
  Given:
  Assume:
  Conclusion: (⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)) = [0, 1]
Proof:
  Let's first prove that (⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)) ⊆ [0, 1]
  · Fix x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
    It suffices to prove that 0 ≤ x and x ≤ 1
    Let's first prove that 0 ≤ x
    · Since x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
        we get that x ∈ [0, 1 + 1 / 1)
      Since x ∈ [0, 1 + 1 / 1)
      we conclude that 0 ≤ x
    Let's now prove that x ≤ 1
    · Assume for contradiction that ¬ (x ≤ 1)
      Since ¬ (x ≤ 1) we get that x > 1
      Since x > 1 we get that x - 1 > 0
      Since x - 1 > 0
        we get N : ℕ such that N ≥ 1 and N > 1 / (x - 1)
      Since N > 1 / (x - 1) and x - 1 > 0
        we get that 1 / N < x - 1
      Since 1 / N < x - 1
        we get that x > 1 + 1 / N
      Since x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n) and N ≥ 1
        we get that x ∈ [0, 1 + 1 / N)
      Since x ∈ [0, 1 + 1 / N)
        we get that x < 1 + 1 / N
      Let's prove it's contradictory
      We conclude by contradicting x < 1 + 1 / N and x > 1 + 1 / N
  Let's now prove that [0, 1] ⊆
      ⋂ (n : ℕ) (_ : n ≥ 1), [0, 1 + 1 / n)
  · Fix x ∈ [0, 1]
    Since x ∈ [0, 1] we get that 0 ≤ x and x ≤ 1
    It suffices to prove that
      ∀ n : ℕ, n ≥ 1 → x ∈ [0, 1 + 1 / n)
    Fix n ≥ 1
    It suffices to prove that 0 ≤ x ∧ x < 1 + 1 / n
    Let's first prove that 0 ≤ x
    · We conclude by hypothesis
    Let's now prove that x < 1 + 1 / n
    · Since n ≥ 1 and x ≤ 1 we conclude that x < 1 + 1 / n
QED
```

Below is an exercise to practice with indexed unions, mirroring Example 2.2.19 above but for `⋃` instead of `⋂`.

::::multilean
```lean
-- Exercise 2.2.35
Exercise "2.2.35"
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

Below is an exercise to practice with an indexed intersection over all of `ℕ` (no `n ≥ 1` restriction).

::::multilean
```lean
-- Exercise 2.2.36a
Exercise "2.2.36a"
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
