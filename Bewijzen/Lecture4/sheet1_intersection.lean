import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
import Bewijzen.Customlib.Sets

open WaterproofGenre
open Verbose.NameLess
open scoped Bewijzen.IntervalNotation
open scoped Bewijzen.PairSetNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma emptySet
addAnonymousGoalSplittingLemma pairSets
addAnonymousGoalSplittingLemma intervalMembership
addAnonymousGoalSplittingLemma pairValueContradictions
addAnonymousGoalSplittingLemma singleInterval

#doc (WaterproofGenre) "Intersection" =>

```lean
-- Example 2.2.3
Example "2.2.3"
  Given: (x : ℝ) (Q : Set ℝ)
  Assume:
  Conclusion: x ∈ [0, ∞) ∩ Q ⇔ x ∈ [0, ∞) ∧ x ∈ Q
Proof:
  Let's first prove that x ∈ [0, ∞) ∩ Q ⇒ x ∈ [0, ∞) ∧ x ∈ Q
  · Assume that x ∈ [0, ∞) ∩ Q
    We conclude by hypothesis
  Let's now prove that x ∈ [0, ∞) ∧ x ∈ Q ⇒ x ∈ [0, ∞) ∩ Q
  · Assume that x ∈ [0, ∞) ∧ x ∈ Q
    We conclude by hypothesis
QED
```

```lean
-- Interval Example
Example "Interval Example"
  Given:
  Assume:
  Conclusion: [0, 2] ∩ [0, 1] is an interval
Proof:
  It suffices to prove that [0, 2] ∩ [0, 1] = [0, 1]
  Let's first prove that [0, 2] ∩ [0, 1] ⊆ [0, 1]
  · Fix x
    Assume that x ∈ [0, 2] ∩ [0, 1]
    Since x ∈ [0, 2] ∩ [0, 1] we get that x ∈ [0, 2] and x ∈ [0, 1]
    We conclude by hypothesis
  Let's now prove that [0, 1] ⊆ [0, 2] ∩ [0, 1]
  · Fix x
    Assume that x ∈ [0, 1]
    Since x ∈ [0, 1] we get that 0 ≤ x and x ≤ 1
    Let's first prove that x ∈ [0, 2]
    · Since x ≤ 1 we get that x ≤ 2
      Since 0 ≤ x and x ≤ 2 we conclude that x ∈ [0, 2]
    Let's now prove that x ∈ [0, 1]
    · We conclude by hypothesis
QED
```

::::multilean
```lean
-- Exercise 2.2.6
Exercise "2.2.6"
  Given:
  Assume:
  Conclusion: [-2, 5) ∩ [4, 7) is an interval
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
-- Proposition 2.2.7
Example "2.2.7"
  Given: (U : Type) (X Y : Set U)
  Assume:
  Conclusion: X ⊆ Y ⇔ X ∩ Y = X
Proof:
  Let's first prove that X ⊆ Y ⇒ X ∩ Y = X
  · Assume that X ⊆ Y
    Let's first prove that X ∩ Y ⊆ X
    · Fix x
      Assume that x ∈ X ∩ Y
      Since x ∈ X ∩ Y we get that x ∈ X and x ∈ Y
      We conclude by hypothesis
    Let's now prove that X ⊆ X ∩ Y
    · Fix x
      Assume that x ∈ X
      Since X ⊆ Y and x ∈ X we get that x ∈ Y
      Let's first prove that x ∈ X
      · We conclude by hypothesis
      Let's now prove that x ∈ Y
      · We conclude by hypothesis
  Let's now prove that X ∩ Y = X ⇒ X ⊆ Y
  · Assume that X ∩ Y = X
    Fix x
    Assume that x ∈ X
    Since X ∩ Y = X and x ∈ X we get that x ∈ X ∩ Y
    Since x ∈ X ∩ Y we get that x ∈ X and x ∈ Y
    We conclude by hypothesis
QED
```

::::multilean
```lean
-- Exercise 2.2.8
Exercise "2.2.8"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: X ∩ ∅ = ∅
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
-- Example 2.2.10
Example "2.2.10"
  Given:
  Assume:
  Conclusion: {0, 2} ∩ {1, 3} = (∅ : Set ℝ)
Proof:
  Let's first prove that {0, 2} ∩ {1, 3} ⊆ (∅ : Set ℝ)
  · Fix x
    Assume that x ∈ {0, 2} ∩ {1, 3}
    Since x ∈ {0, 2} ∩ {1, 3} we get that x ∈ {0, 2} and x ∈ {1, 3}
    Since x ∈ {0, 2} we get that x = 0 ∨ x = 2
    Let's prove it's contradictory
    We discuss depending on whether x = 0 or x = 2
    · Assume that x = 0
      Since x ∈ {1, 3} we get that x = 1 ∨ x = 3
      We discuss depending on whether x = 1 or x = 3
      · Assume that x = 1
        Since x = 0 and x = 1 we conclude that False
      · Assume that x = 3
        Since x = 0 and x = 3 we conclude that False
    · Assume that x = 2
      Since x ∈ {1, 3} we get that x = 1 ∨ x = 3
      We discuss depending on whether x = 1 or x = 3
      · Assume that x = 1
        Since x = 2 and x = 1 we conclude that False
      · Assume that x = 3
        Since x = 2 and x = 3 we conclude that False
  Let's now prove that (∅ : Set ℝ) ⊆ {0, 2} ∩ {1, 3}
  · Fix x
    Assume that x ∈ (∅ : Set ℝ)
    Let's prove it's contradictory
    We conclude by hypothesis
QED
```
