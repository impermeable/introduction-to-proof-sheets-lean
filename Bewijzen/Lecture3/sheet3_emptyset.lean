import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Lists
open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
open scoped Bewijzen.IntervalNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma emptySet
addAnonymousGoalSplittingLemma intervalMembership

#doc (WaterproofGenre) "Empty Set" =>

```lean
Example "2.1.22"
  Given:
  Assume:
  Conclusion: [0] = ∅
Proof:
  It suffices to prove that ∀ x, x ∈ [0] ⇒ False
  Fix x ∈ [0]
  We conclude by contradicting x < 0
QED
```

::::multilean
```lean
Exercise "2.1.23a"
  Given: (a b : ℝ)
  Assume:
  Conclusion: [a, b] = ∅ ⇔ a > b
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
Exercise "2.1.23b"
  Given: (a b : ℝ)
  Assume:
  Conclusion: (a, b) = ∅ ⇔ a ≥ b
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
Exercise "2.1.24a"
  Given: (U : Type) (E : Set U) (p : U → Prop)
  Assume: (_ : E = ∅)
  Conclusion: ∀ x ∈ E, p x
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
Exercise "2.1.24b"
  Given: (U : Type) (E : Set U) (p : U → Prop)
  Assume: (_ : E = ∅)
  Conclusion: ¬ ∃ x ∈ E, p x
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
Example "2.1.25"
  Given: (U : Type) (E E' : Set U)
  Assume: (_ : E = ∅) (_ : E' = ∅)
  Conclusion: E = E'
Proof:
  Let's first prove that E ⊆ E'
  · Fix x ∈ E
    Let's prove it's contradictory
    We conclude by contradicting E = ∅ and x ∈ E
  Let's now prove that E' ⊆ E
  · Fix x ∈ E'
    Let's prove it's contradictory
    We conclude by contradicting E' = ∅ and x ∈ E'
QED
```

::::multilean
```lean
Exercise "2.1.27"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: ∅ ⊆ X
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
