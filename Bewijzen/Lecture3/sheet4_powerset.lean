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

In Waterproof, the powerset of `X` is denoted as `𝒫 X` (`𝒫` is written as `\McP`), and `A ∈ 𝒫 X` is by definition equivalent to `A ⊆ X`.
From this, you can use `It suffices to prove that ...` if the statement `A ∈ 𝒫 X` is in the goal, and you can use `Since ... we get that ...` if the statement `A ∈ 𝒫 X` is in the assumptions.
In both cases, Waterproof will automatically use the definition of the power set to complete the proof step.
Below is an example.

```lean
Example "2.1.29_definition"
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

Below are several exercises on powersets.

::::multilean
```lean
Exercise "2.1.32a"
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
Exercise "2.1.32b"
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
Exercise "2.1.35"
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

Below are two options for exercise 2.1.36a. Prove the one that is true.

::::multilean
```lean
Exercise "2.1.36b (true)"
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
Exercise "2.1.36b (false)"
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
