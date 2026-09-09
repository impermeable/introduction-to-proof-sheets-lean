import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
import Bewijzen.Customlib.Sets

open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
open scoped Bewijzen.IntervalNotation
open scoped Bewijzen.PairSetNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma emptySet
addAnonymousGoalSplittingLemma pairSets
addAnonymousGoalSplittingLemma intervalMembership
addAnonymousGoalSplittingLemma singleInterval

#doc (WaterproofGenre) "Intersection" =>

This exercise sheet is for Section 2.2 Set Operations from the book Infinite Descent into Mathematics.
First, we will prove statements involving the intersection operation (∩).
Waterproof can unfold `a ∈ X ∩ Y` using `It suffices to prove that ...` and `Since ... we get that ...`.
Below is an example.

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

Before doing an exercise, it helps to understand how to prove that a set is an interval in Waterproof.
This is done by using `It suffices to prove that ...`.
In the following line, you choose the interval you want to show the set equals.
To illustrate this, a proof is shown below.

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

The following exercise is to practice with intersections (∩).

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

Below is another example of a proof with intersection.

```lean
-- Proposition 2.2.8
Example "2.2.8"
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
      Since x ∈ X and x ∈ Y we conclude that x ∈ X ∩ Y
  Let's now prove that X ∩ Y = X ⇒ X ⊆ Y
  · Assume that X ∩ Y = X
    Fix x
    Assume that x ∈ X
    Since X ∩ Y = X and x ∈ X we get that x ∈ X ∩ Y
    Since x ∈ X ∩ Y we get that x ∈ X and x ∈ Y
    We conclude by hypothesis
QED
```

Below is another exercise to practice using intersections.

::::multilean
```lean
-- Exercise 2.2.9a
Exercise "2.2.9a"
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

To show that two sets `A` and `B` are disjoint in Waterproof, use `It suffices to prove that A ∩ B is empty`.
This can then be unfolded using the definition from Section 2.1.

Below is a slightly adapted version of the textbook's Example 2.2.10 to make
the proof less verbose.

```lean
-- Example 2.2.11
Example "2.2.11"
  Given:
  Assume:
  Conclusion: {0, 2} is disjoint from {1, 3}
Proof:
  It suffices to prove that {0, 2} ∩ {1, 3} is empty
  It suffices to prove that ∀ x ∈ {0, 2} ∩ {1, 3}, False
  · Fix x ∈ {0, 2} ∩ {1, 3}
    Since x ∈ {0, 2} ∩ {1, 3} we get that x ∈ {0, 2} and x ∈ {1, 3}
    Since x ∈ {0, 2} we get that x = 0 ∨ x = 2
    We discuss depending on whether x = 0 or x = 2
    · Assume that x = 0
      Since x ∈ {1, 3} we get that x = 1 ∨ x = 3
      We discuss depending on whether x = 1 or x = 3
      · Assume that x = 1
        Since x = 1 and x = 0 we get that 0 = 1
        We conclude by contradicting 0 = 1
      · Assume that x = 3
        Since x = 0 and x = 3 we get that 0 = 3
        We conclude by contradicting 0 = 3
    · Assume that x = 2
      Since x ∈ {1, 3} we get that x = 1 ∨ x = 3
      We discuss depending on whether x = 1 or x = 3
      · Assume that x = 1
        Since x = 1 and x = 2 we get that 1 = 2
        We conclude by contradicting 1 = 2
      · Assume that x = 3
        Since x = 2 and x = 3 we get that 2 = 3
        We conclude by contradicting 2 = 3
QED
```
