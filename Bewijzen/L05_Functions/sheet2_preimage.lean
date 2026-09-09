import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess

-- Lets a written type X denote the set of all its elements (issue #67).
readTypesAsSets

addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma imageMembership

#doc (WaterproofGenre) "Function Preimages" =>

This exercise sheet continues Section 3.1 Functions from the book Infinite Descent into Mathematics, now working with preimages.
In Waterproof `f ⁻¹' V` is the preimage of `V` under `f`, and `x ∈ f ⁻¹' V` by definition means exactly `f(x) ∈ V`, so you can move between the two without a separate step.
The example below shows how the image and the preimage interact.

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

For technical reasons, Waterproof considers the empty set in the exercise below to have a universe of discourse of X or Y. Most of the time this will be determined automatically, but sometimes it cannot. If you get a weird error while using the empty set, try using `(∅ : Set X)` or `(∅ : Set Y)` instead of just `∅`.

::::multilean
```lean
Exercise "3.1.41a"
  Given: (X Y : Type) (f : X → Y)
  Assume:
  Conclusion: f ⁻¹' ∅ = ∅
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
Exercise "3.1.41b"
  Given: (X Y : Type) (f : X → Y)
  Assume:
  Conclusion: f ⁻¹' Y = X
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
