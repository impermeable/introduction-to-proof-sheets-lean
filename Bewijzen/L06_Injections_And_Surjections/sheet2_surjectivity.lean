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

A function `f : X → Y` is surjective when every `y : Y` is of the form `f(x)`. In
Waterproof you can unfold `f is surjective` into that statement, both as a goal and
from an assumption. The example below shows the syntax.

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
  Given: (X : Type) (f : X → Set X)
  Assume:
  Conclusion: ¬ (f is surjective)
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

A function is bijective when it is both injective and surjective, so `f is bijective`
is equivalent to `f is injective ∧ f is surjective`.

::::multilean
```lean
Exercise "3.2.20"
  Given: (X Y Z : Type) (f : X → Y) (g : Y → Z)
  Assume:
  Conclusion: f is bijective ⇒ g is bijective ⇒ (g ∘ f) is bijective
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
