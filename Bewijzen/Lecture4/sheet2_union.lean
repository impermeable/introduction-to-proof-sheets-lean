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

Statements using unions (∪) can be proved in Waterproof using `It suffices to prove that ...` and `Since ... we get that ...`.
All of these use the following equivalence,

`x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B`

Note that this is similar to intersections, but instead of conjunctions (and), it uses disjunctions (or).
Below are exercises and examples on using unions.

::::multilean
```lean
-- Exercise 2.2.25
Exercise "2.2.25"
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
-- Exercise 2.2.26
Exercise "2.2.26"
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

Distributivity laws — combining intersection and union

```lean
-- Example 2.2.27
Example "2.2.27"
  Given: (U : Type) (X Y Z : Set U)
  Assume:
  Conclusion: X ∩ (Y ∪ Z) = (X ∩ Y) ∪ (X ∩ Z)
Proof:
  Let's first prove that X ∩ (Y ∪ Z) ⊆ (X ∩ Y) ∪ (X ∩ Z)
  · Fix x ∈ X ∩ (Y ∪ Z)
    Since x ∈ X ∩ (Y ∪ Z) we get that x ∈ X and x ∈ Y ∨ x ∈ Z
    We discuss depending on whether x ∈ Y or x ∈ Z
    · Assume that x ∈ Y
      Let's prove that x ∈ X ∩ Y
      Since x ∈ X and x ∈ Y we conclude that x ∈ X ∩ Y
    · Assume that x ∈ Z
      Let's prove that x ∈ X ∩ Z
      Since x ∈ X and x ∈ Z we conclude that x ∈ X ∩ Z
  Let's now prove that (X ∩ Y) ∪ (X ∩ Z) ⊆ X ∩ (Y ∪ Z)
  · Fix x ∈ (X ∩ Y) ∪ (X ∩ Z)
    We discuss depending on whether x ∈ X ∩ Y or x ∈ X ∩ Z
    · Assume that x ∈ X ∩ Y
      Since x ∈ X ∩ Y we get that x ∈ X and x ∈ Y
      It suffices to prove that x ∈ X ∧ x ∈ Y ∪ Z
      Let's first prove that x ∈ X
      · We conclude by hypothesis
      Let's now prove that x ∈ Y ∪ Z
      · Let's prove that x ∈ Y
        · We conclude by hypothesis
    · Assume that x ∈ X ∩ Z
      Since x ∈ X ∩ Z we get that x ∈ X and x ∈ Z
      It suffices to prove that x ∈ X ∧ x ∈ Y ∪ Z
      Let's first prove that x ∈ X
      · We conclude by hypothesis
      Let's now prove that x ∈ Y ∪ Z
      · Let's prove that x ∈ Z
        · We conclude by hypothesis
QED
```

::::multilean
```lean
-- Exercise 2.2.28
Exercise "2.2.28"
  Given: (U : Type) (X Y Z : Set U)
  Assume:
  Conclusion: X ∪ (Y ∩ Z) = (X ∪ Y) ∩ (X ∪ Z)
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
