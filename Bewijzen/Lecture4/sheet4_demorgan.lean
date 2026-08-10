import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists
import Bewijzen.Customlib.Sets

open WaterproofGenre
open Verbose.NameLess

configureAnonymousCaseSplittingLemmas caseSplittingClassical
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma setDifference
addAnonymousGoalSplittingLemma negatedMembership

#doc (WaterproofGenre) "De Morgan's Laws" =>

```lean
-- Example 2.2.33 (a)
Example "2.2.33 (a)"
  Given: (𝒰 : Type) (X : Set 𝒰) (A B : Set 𝒰)
  Assume:
  Conclusion: X \ (A ∪ B) = (X \ A) ∩ (X \ B)
Proof:
  Let's first prove that X \ (A ∪ B) ⊆ (X \ A) ∩ (X \ B)
  · Fix x
    Assume that x ∈ X \ (A ∪ B)
    Since x ∈ X \ (A ∪ B) we get that x ∈ X and x ∉ A ∪ B
    Since x ∉ A ∪ B we get that x ∉ A and x ∉ B
    It suffices to prove that x ∈ X \ A ∧ x ∈ X \ B
    Let's first prove that x ∈ X \ A
    · Let's first prove that x ∈ X
      · We conclude by hypothesis
      Let's now prove that x ∉ A
      · We conclude by hypothesis
    Let's now prove that x ∈ X \ B
    · Let's first prove that x ∈ X
      · We conclude by hypothesis
      Let's now prove that x ∉ B
      · We conclude by hypothesis
  Let's now prove that (X \ A) ∩ (X \ B) ⊆ X \ (A ∪ B)
  · Fix x
    Assume that x ∈ (X \ A) ∩ (X \ B)
    Since x ∈ (X \ A) ∩ (X \ B)
    we get that x ∈ X \ A and x ∈ X \ B
    Since x ∈ X \ A we get that x ∈ X and x ∉ A
    Since x ∈ X \ B we get that x ∉ B
    It suffices to prove that x ∈ X ∧ x ∉ A ∪ B
    Let's first prove that x ∈ X
    · We conclude by hypothesis
    Let's now prove that x ∉ A ∪ B
    · Since x ∉ A and x ∉ B we conclude that x ∉ A ∪ B
QED
```

::::multilean
```lean
-- Exercise 2.2.34 (b)
Exercise "2.2.34 (b)"
  Given: (𝒰 : Type) (X : Set 𝒰) (A B : Set 𝒰)
  Assume:
  Conclusion: X \ (A ∩ B) = (X \ A) ∪ (X \ B)
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
