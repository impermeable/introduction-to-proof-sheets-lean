import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess
open Function

addAnonymousGoalSplittingLemma equalityBridges
addAnonymousGoalSplittingLemma linearEquations

configureAnonymousCaseSplittingLemmas caseSplittingClassical

#doc (WaterproofGenre) "Injective Functions" =>

A function `f` is injective when `f(a) = f(b)` implies `a = b`. To use or prove
injectivity, unfold it with
`It suffices to prove that ∀ a b : X, f(a) = f(b) ⇒ a = b`.

```lean
Example "3.2.4"
  Given: (X Y Z : Type) (f : X → Y) (g : Y → Z)
  Assume:
  Conclusion: f is injective ⇒ g is injective ⇒ (g ∘ f) is injective
Proof:
  Assume that f is injective
  Assume that g is injective
  It suffices to prove that ∀ a b : X, (g ∘ f)(a) = (g ∘ f)(b) ⇒ a = b
  Fix a
  Fix b
  Assume that (g ∘ f)(a) = (g ∘ f)(b)
  Since (g ∘ f)(a) = (g ∘ f)(b) we get that g(f(a)) = g(f(b))
  Since g is injective and g(f(a)) = g(f(b)) we get that f(a) = f(b)
  Since f is injective and f(a) = f(b) we conclude that a = b
QED
```

::::multilean
```lean
Exercise "3.2.5"
  Given: (X Y Z : Type) (f : X → Y) (g : Y → Z)
  Assume:
  Conclusion: (g ∘ f) is injective ⇒ f is injective
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
Exercise "3.2.8"
  Given: (a : ℝ) (b : ℝ)
  Assume: (_ : b ≠ 0)
  Conclusion: (fun t : ℝ => a + b * t) is injective
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
