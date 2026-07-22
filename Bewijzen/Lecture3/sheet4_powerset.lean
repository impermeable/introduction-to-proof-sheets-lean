import WaterproofGenre
import Verbose.English.All
import Mathlib.Order.Interval.Set.Basic
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Lists
open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
open scoped Set

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma emptySet

Lemma example_2_1_8 "2.1.8"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: X ⊆ X
Proof:
  Fix x ∈ X
  We conclude by hypothesis
QED

Lemma exercise_2_1_27 "2.1.27"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: ∅ ⊆ X
Proof:
  Fix x ∈ (∅ : Set U)
  Let's prove it's contradictory
  We conclude by contradicting x ∈ (∅ : Set U)
QED

#doc (WaterproofGenre) "Power Set" =>

```lean
Example "2.1.28"
  Given: (U : Type) (X Y : Set U)
  Assume:
  Conclusion: X ⊆ Y ⇔ X ∈ 𝒫 Y
Proof:
  Let's first prove that X ⊆ Y ⇒ X ∈ 𝒫 Y
  · Assume that X ⊆ Y
    We conclude by hypothesis
  Let's now prove that X ∈ 𝒫 Y ⇒ X ⊆ Y
  · Assume that X ∈ 𝒫 Y
    We conclude by hypothesis
QED
```

::::multilean
```lean
Exercise "2.1.31a"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: ∅ ∈ 𝒫 X
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
Exercise "2.1.31b"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: X ∈ 𝒫 X
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
Exercise "2.1.34"
  Given: (U : Type) (X Y : Set U)
  Assume: (_ : X ⊆ Y)
  Conclusion: 𝒫 X ⊆ 𝒫 Y
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

Below are two options for exercise 2.1.36a; only one of them is true. Prove the one that is true.

::::multilean
```lean
Exercise "2.1.36a (true)"
  Given: (U : Type)
  Assume:
  Conclusion: 𝒫 (∅ : Set U) ∈ 𝒫 (𝒫 (∅ : Set U))
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
Exercise "2.1.36a (false)"
  Given: (U : Type)
  Assume:
  Conclusion: ¬ (𝒫 (∅ : Set U) ∈ 𝒫 (𝒫 (∅ : Set U)))
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
