import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess
open Set (univ)

addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma imageMembership

#doc (WaterproofGenre) "Function Preimages" =>


```lean
Example "3.1.39"
  Given: (X Y : Type) (f : X → Y) (U : Set X) (V : Set Y)
  Assume:
  Conclusion: f '' U ⊆ V ⇔ U ⊆ f ⁻¹' V
Proof:
  Let's first prove that f '' U ⊆ V ⇒ U ⊆ f ⁻¹' V
  · Assume that f '' U ⊆ V
    Fix x ∈ U
    It suffices to prove that f(x) ∈ V
    Since f '' U ⊆ V it suffices to prove that f(x) ∈ f '' U
    Since x ∈ U we conclude that f(x) ∈ f '' U
  Let's now prove that U ⊆ f ⁻¹' V ⇒ f '' U ⊆ V
  · Assume that U ⊆ f ⁻¹' V
    Fix y ∈ f '' U
    Since y ∈ f '' U we get x such that x ∈ U and f(x) = y
    Since f(x) = y it suffices to prove that f(x) ∈ V
    Since U ⊆ f ⁻¹' V and x ∈ U we conclude that f(x) ∈ V
QED
```

::::multilean
```lean
Exercise "3.1.40a"
  Given: (X Y : Type) (f : X → Y)
  Assume:
  Conclusion: f ⁻¹' (∅ : Set Y) = (∅ : Set X)
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
Exercise "3.1.40b"
  Given: (X Y : Type) (f : X → Y)
  Assume:
  Conclusion: f ⁻¹' (univ : Set Y) = (univ : Set X)
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
