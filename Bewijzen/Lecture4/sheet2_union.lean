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
addAnonymousGoalSplittingLemma unionMembership
addAnonymousGoalSplittingLemma singleInterval

#doc (WaterproofGenre) "Union" =>

::::multilean
```lean
-- Exercise 2.2.20
Exercise "2.2.20"
  Given:
  Assume:
  Conclusion: [-2, 5) ∪ [4, 7) is an interval
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
-- Exercise 2.2.21
Exercise "2.2.21"
  Given: (U : Type) (X Y : Set U)
  Assume:
  Conclusion: X ⊆ Y ⇔ X ∪ Y = Y
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

-- Distributivity laws — combining intersection and union
```lean
-- Example 2.2.22
Example "2.2.22"
  Given: (U : Type) (X Y W : Set U)
  Assume:
  Conclusion: X ∩ (Y ∪ W) = (X ∩ Y) ∪ (X ∩ W)
Proof:
  Let's first prove that X ∩ (Y ∪ W) ⊆ (X ∩ Y) ∪ (X ∩ W)
  · Fix a
    Assume that a ∈ X ∩ (Y ∪ W)
    Since a ∈ X ∩ (Y ∪ W) we get that a ∈ X and a ∈ Y ∪ W
    Since a ∈ Y ∪ W we get that a ∈ Y ∨ a ∈ W
    We discuss depending on whether a ∈ Y or a ∈ W
    · Assume that a ∈ Y
      Let's prove that a ∈ X ∩ Y
      · It suffices to prove that a ∈ X ∧ a ∈ Y
        Let's first prove that a ∈ X
        · We conclude by hypothesis
        Let's now prove that a ∈ Y
        · We conclude by hypothesis
    · Assume that a ∈ W
      Let's prove that a ∈ X ∩ W
      · It suffices to prove that a ∈ X ∧ a ∈ W
        Let's first prove that a ∈ X
        · We conclude by hypothesis
        Let's now prove that a ∈ W
        · We conclude by hypothesis
  Let's now prove that (X ∩ Y) ∪ (X ∩ W) ⊆ X ∩ (Y ∪ W)
  · Fix a
    Assume that a ∈ (X ∩ Y) ∪ (X ∩ W)
    Since a ∈ (X ∩ Y) ∪ (X ∩ W) we get that a ∈ X ∩ Y ∨ a ∈ X ∩ W
    We discuss depending on whether a ∈ X ∩ Y or a ∈ X ∩ W
    · Assume that a ∈ X ∩ Y
      Since a ∈ X ∩ Y we get that a ∈ X and a ∈ Y
      It suffices to prove that a ∈ X ∧ a ∈ Y ∪ W
      Let's first prove that a ∈ X
      · We conclude by hypothesis
      Let's now prove that a ∈ Y ∪ W
      · Let's prove that a ∈ Y
        · We conclude by hypothesis
    · Assume that a ∈ X ∩ W
      Since a ∈ X ∩ W we get that a ∈ X and a ∈ W
      It suffices to prove that a ∈ X ∧ a ∈ Y ∪ W
      Let's first prove that a ∈ X
      · We conclude by hypothesis
      Let's now prove that a ∈ Y ∪ W
      · Let's prove that a ∈ W
        · We conclude by hypothesis
QED
```

::::multilean
```lean
-- Exercise 2.2.23
Exercise "2.2.23"
  Given: (U : Type) (X Y W : Set U)
  Assume:
  Conclusion: X ∪ (Y ∩ W) = (X ∪ Y) ∩ (X ∪ W)
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
