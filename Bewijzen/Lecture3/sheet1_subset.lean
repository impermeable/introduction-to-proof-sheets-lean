import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
open WaterproofGenre
open Verbose.NameLess
open scoped Bewijzen.IntervalNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma intervalSubset

#doc (WaterproofGenre) "Subset" =>

```lean
Lemma example_2_1_8 "2.1.8"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: X ⊆ X
Proof:
  Fix x ∈ X
  We conclude by hypothesis
QED
```

```lean
Example "2.1.9"
  Given: (a b c d : ℝ)
  Assume: (_ : a < c) (_ : c < d) (_ : d < b)
  Conclusion: [c, d] ⊆ (a, b)
Proof:
  Fix x ∈ [c, d]
  Since x ∈ [c, d] we get that c ≤ x and x ≤ d
  It suffices to prove that a < x ∧ x < b
  Let's first prove that a < x
  · Since a < c and c ≤ x we conclude that a < x
  Let's now prove that x < b
  · Since x ≤ d and d < b we conclude that x < b
QED
```

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
