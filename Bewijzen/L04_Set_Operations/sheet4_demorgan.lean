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
addAnonymousGoalSplittingLemma not_mem_left_of_not_mem_union
addAnonymousGoalSplittingLemma not_mem_or_of_not_mem_inter


#doc (WaterproofGenre) "De Morgan's Laws" =>

The following example proves one of De Morgan's laws for sets, which establish the relationship between set difference and set operations.

```lean
-- Example 2.2.44a
Example "2.2.44a"
  Given: (𝒰 : Type) (X : Set 𝒰) (A B : Set 𝒰)
  Assume:
  Conclusion: X \ (A ∪ B) = (X \ A) ∩ (X \ B)
Proof:
  Let's first prove that X \ (A ∪ B) ⊆ (X \ A) ∩ (X \ B)
  · Fix x ∈ X \ (A ∪ B)
    Since x ∈ X \ (A ∪ B) we get that x ∈ X and x ∉ A ∪ B
    Since x ∉ A ∪ B we get that x ∉ A and x ∉ B
    -- SHORTCUT
    -- Since x ∈ X, x ∉ A and x ∉ B we get that x ∈ (X \ A) ∩ (X \ B) 
    It suffices to prove that x ∈ X \ A ∧ x ∈ X \ B
    Let's first prove that x ∈ X \ A
    Since x ∈ X and x ∉ A we conclude that x ∈ X \ A
    Let's now prove that x ∈ X \ B
    Since x ∈ X and x ∉ B we conclude that x ∈ X \ B
  Let's now prove that (X \ A) ∩ (X \ B) ⊆ X \ (A ∪ B)
  · Fix x ∈ (X \ A) ∩ (X \ B)
    Since x ∈ (X \ A) ∩ (X \ B)
      we get that x ∈ X \ A and x ∈ X \ B
    Since x ∈ X \ A we get that x ∈ X and x ∉ A
    Since x ∈ X \ B we get that x ∉ B
    Since x ∉ A and x ∉ B we get that x ∉ A ∪ B
    Since x ∈ X and x ∉ A ∪ B we conclude that x ∈ X \ (A ∪ B)
QED
```

Below is an exercise to prove another De Morgan's law.

::::multilean
```lean
-- Exercise 2.2.45b
Exercise "2.2.45b"
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
