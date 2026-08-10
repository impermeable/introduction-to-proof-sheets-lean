import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess
open Function

addAnonymousGoalSplittingLemma equalityBridges
addAnonymousGoalSplittingLemma setEqualityTransport
addAnonymousGoalSplittingLemma bijectivity

configureAnonymousCaseSplittingLemmas caseSplittingClassical

#doc (WaterproofGenre) "Surjective Functions" =>

A function `f : X → Y` is surjective when every `y : Y` is of the form `f(x)`.
To use or prove surjectivity, unfold it with
`It suffices to prove that ∀ y : Y, ∃ x : X, f(x) = y`.

```lean
Example "Surjectivity Example"
  Given:
  Assume:
  Conclusion: (fun x : ℝ => x / 2) is surjective
Proof:
  It suffices to prove that ∀ y : ℝ, ∃ x : ℝ, x / 2 = y
  Fix y
  Let's prove that 2 * y works
  We compute
QED
```

::::multilean
```lean
Exercise "3.2.16"
  Given: (X : Type) (F : X → Set X)
  Assume:
  Conclusion: ¬ (F is surjective)
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
Exercise "3.2.20"
  Given: (X Y Z : Type) (F : X → Y) (G : Y → Z)
  Assume:
  Conclusion: F is bijective ⇒ G is bijective ⇒ (G ∘ F) is bijective
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
