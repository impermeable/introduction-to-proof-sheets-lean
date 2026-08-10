import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess

configureAnonymousCaseSplittingLemmas caseSplittingClassical

#doc (WaterproofGenre) "Function Images" =>



```lean
Example "3.1.35"
  Given: (X Y : Type) (g : X → Y) (U V : Set X)
  Assume:
  Conclusion: g '' (U ∩ V) ⊆ g '' U ∩ g '' V
Proof:
  Fix y ∈ g '' (U ∩ V)
  Since y ∈ g '' (U ∩ V) we get x such that
    x ∈ U ∩ V and g(x) = y
  Since x ∈ U ∩ V we get that x ∈ U and x ∈ V
  Let's first prove that y ∈ g '' U
  · Let's prove that x works
    Since x ∈ U and g(x) = y we conclude that x ∈ U ∧ g(x) = y
  Let's now prove that y ∈ g '' V
  · Let's prove that x works
    Since x ∈ V and g(x) = y we conclude that x ∈ V ∧ g(x) = y
QED
```

::::multilean
```lean
Exercise "3.1.36a"
  Given: (X Y : Type) (g : X → Y) (U V : Set X)
  Assume:
  Conclusion: g '' U ∩ g '' V ⊆ g '' (U ∩ V)
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
  Given: (X Y : Type) (g : X → Y) (U V : Set X)
  Assume:
  Conclusion: g '' (U ∪ V) ⊆ g '' U ∪ g '' V
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
  Given: (X Y : Type) (g : X → Y) (U V : Set X)
  Assume:
  Conclusion: g '' U ∪ g '' V ⊆ g '' (U ∪ V)
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
