import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Lists
open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
open scoped Bewijzen.IntervalNotation
open scoped Bewijzen.EmptySetNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma emptySet
addAnonymousGoalSplittingLemma intervalMembership
addAnonymousGoalSplittingLemma ge_and_lt_real_false

#doc (WaterproofGenre) "Empty Set" =>

Below is an example of how Waterproof proves that a set is empty.
This is done by assuming the set has an element and then finding a contradiction.

```lean
Example "2.1.22"
  Given:
  Assume:
  Conclusion: [0] is empty
Proof:
  It suffices to prove that ∀ x, x ∈ [0] ⇒ False
  Fix x ∈ [0]
  We conclude by contradicting x < 0
QED
```

Below are five exercises to practice using empty sets.

::::multilean
```lean
Exercise "2.1.23a"
  Given: (a b : ℝ)
  Assume:
  Conclusion: [a, b] is empty ⇔ a > b
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
  Conclusion: (a, b) is empty ⇔ a ≥ b
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

In the following exercises `U : Type` means that `U` is some universe set, and `E : Set U` means that `E` is a subset of `U`.

::::multilean
```lean
Exercise "2.1.24a"
  Given: (U : Type) (E : Set U) (p : U → Prop)
  Assume: (_ : E is empty)
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
  Assume: (_ : E is empty)
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

Until now, we have proved statements about whether sets are empty, but it turns out there can only be one empty set.
This is proved by the following theorem.

```lean
Example "2.1.25"
  Given: (U : Type) (E E' : Set U)
  Assume: (_ : E is empty) (_ : E' is empty)
  Conclusion: E = E'
Proof:
  Let's first prove that E ⊆ E'
  · Fix x ∈ E
    Let's prove it's contradictory
    We conclude by contradicting E is empty and x ∈ E
  Let's now prove that E' ⊆ E
  · Fix x ∈ E'
    Let's prove it's contradictory
    We conclude by contradicting E' is empty and x ∈ E'
QED
```

From now on, we will use `∅` to denote the empty set.
We can do this since there is only one empty set.
Below is an exercise using `∅` with two options; only one of them is true. Prove the one that is true.

When working with the empty set in these exercise,
you might need to specify that the empty set is a subset of the universe set `U`.
This can be done by writing `(∅ : Set U)` instead of plain `∅`.

::::multilean
```lean
Exercise "2.1.27a (true)"
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

::::multilean
```lean
Exercise "2.1.27a (false)"
  Given: (U : Type) (X : Set U)
  Assume:
  Conclusion: ¬ (∅ ⊆ X)
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
