import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
open scoped Bewijzen.IntervalNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma intervalSubset

#doc (WaterproofGenre) "Subset" =>

This exercise sheet is for Section 2.1 Sets from the book Infinite Descent into Mathematics.
Before starting this exercise sheet, first read and complete the exercises from the book up to the section on subsets.

The example below shows how to work with subset notation ⊆. In Waterproof `X ⊆ Y` by definition means that `∀ x ∈ X, x ∈ Y`.
We can unfold such a definition using `It suffices to prove that ...`, when the definition to unfold appears in the goal.

```lean
Example "2.1.8"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: X ⊆ X
Proof:
  It suffices to prove that ∀ x ∈ X, x ∈ X
  Fix x ∈ X
  We conclude by hypothesis
QED
```

Below is another example with ⊆ in the goal.

```lean
Example "2.1.9"
  Given: (a b c d : ℝ)
  Assume: (_ : a < c) (_ : c < d) (_ : d < b)
  Conclusion: [c, d] ⊆ (a, b)
Proof:
  It suffices to prove that ∀ x ∈ [c, d], x ∈ (a, b)
  Fix x ∈ [c, d]
  Since x ∈ [c, d] we get that c ≤ x and x ≤ d
  It suffices to prove that a < x ∧ x < b
  Let's first prove that a < x
  · Since a < c and c ≤ x we conclude that a < x
  Let's now prove that x < b
  · Since x ≤ d and d < b we conclude that x < b
QED
```

Below is another example, but here the subset definition is in the assumption.
Such assumption can be applied to an element of the smaller set using `Since ... we get that ...`.

```lean
Example "2.1.12"
  Given: (U : Type) (X Y W : Set U)
  Assume: (_ : X ⊆ Y) (_ : Y ⊆ W)
  Conclusion: X ⊆ W
Proof:
  Fix x ∈ X
  Since X ⊆ Y and x ∈ X we get that x ∈ Y
  Since Y ⊆ W and x ∈ Y we conclude that x ∈ W
QED
```

Below is an exercise on working with subsets.

::::multilean
```lean
Exercise "2.1.10"
  Given: (a b c d : ℝ)
  Assume: (_ : a < b) (_ : c < d)
  Conclusion: [a, b) ⊆ (c, d] ⇔ a > c ∧ b ≤ d
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
