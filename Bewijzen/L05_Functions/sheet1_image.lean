import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess

configureAnonymousCaseSplittingLemmas caseSplittingClassical

#doc (WaterproofGenre) "Function Images" =>

This exercise sheet is for Section 3.1 Functions from the book Infinite Descent into Mathematics.
Before starting, read and complete the exercises from the book up to the section on images and preimages.

The example below shows how to work with the image of a set under a function. In Waterproof `f '' U` is the image of `U` under `f`, and `y ∈ f '' U` by definition means that there exists an `x ∈ U` with `f(x) = y`.
To prove such a membership in the goal, provide a witness using `Let's prove that x works`. To use such a membership from an assumption, unpack it using `Since y ∈ f '' U we get x such that x ∈ U and f(x) = y`.

```lean
Example "3.1.35"
  Given: (X Y : Type) (f : X → Y) (U V : Set X)
  Assume:
  Conclusion: f '' (U ∩ V) ⊆ f '' U ∩ f '' V
Proof:
  Fix y ∈ f '' (U ∩ V)
  Since y ∈ f '' (U ∩ V) we get x such that
    x ∈ U ∩ V and f(x) = y
  Since x ∈ U ∩ V we get that x ∈ U and x ∈ V
  Let's first prove that y ∈ f '' U
  · Let's prove that x works
    Since x ∈ U and f(x) = y we conclude that x ∈ U ∧ f(x) = y
  Let's now prove that y ∈ f '' V
  · Let's prove that x works
    Since x ∈ V and f(x) = y we conclude that x ∈ V ∧ f(x) = y
QED
```

Below are three exercises. Not all of them are provable, since these are True or False questions. For any statements that are false, work out a counter-example example on paper.

::::multilean
```lean
Exercise "3.1.36a"
  Given: (X Y : Type) (f : X → Y) (U V : Set X)
  Assume:
  Conclusion: f '' U ∩ f '' V ⊆ f '' (U ∩ V)
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
Exercise "3.1.36b"
  Given: (X Y : Type) (f : X → Y) (U V : Set X)
  Assume:
  Conclusion: f '' (U ∪ V) ⊆ f '' U ∪ f '' V
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
Exercise "3.1.36c"
  Given: (X Y : Type) (f : X → Y) (U V : Set X)
  Assume:
  Conclusion: f '' U ∪ f '' V ⊆ f '' (U ∪ V)
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
