import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess
open Function

addAnonymousGoalSplittingLemma equalityBridges
addAnonymousGoalSplittingLemma complementMembership
addAnonymousGoalSplittingLemma subsetTheory

configureAnonymousCaseSplittingLemmas caseSplittingClassical

-- The specific function used in Exercise 3.2.39a
noncomputable def F : ℝ → ℝ := fun x => (2 * x + 1) / 3

-- The specific function used in Exercise 3.2.39b
def G : Set ℕ → Set ℕ := fun A => Aᶜ

#doc (WaterproofGenre) "Inverse Functions" =>

A function `g` is a left inverse of `f : X → Y` when `∀ x : X, g(f(x)) = x`,
and a right inverse when `∀ y : Y, f(g(y)) = y`. We say `g` is an inverse of
`f` when it is both, and you can use that `g is an inverse of f` means
`g is a left inverse of f ∧ g is a right inverse of f`.

```lean
Example "Left inverse of the identity"
  Given:
  Assume:
  Conclusion: ∃ G : ℝ → ℝ, G is a left inverse of id
Proof:
  Let's prove that id works
  It suffices to prove that ∀ x : ℝ, id(id(x)) = x
  Fix x
  We compute
QED
```

::::multilean
```lean
Exercise "3.2.21"
  Given: (X Y : Type) (F : X → Y)
  Assume: (_ : F has a left inverse)
  Conclusion: F is injective
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

`F : ℝ → ℝ` is the function `F x = (2 * x + 1) / 3`


::::multilean
```lean
Exercise "3.2.39a"
  Given:
  Assume:
  Conclusion: ∃ G : ℝ → ℝ, G is an inverse of F
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

`G : Set ℕ → Set ℕ` is the function `G A = Aᶜ`.

::::multilean
```lean
Exercise "3.2.39b"
  Given:
  Assume:
  Conclusion: ∃ H : Set ℕ → Set ℕ, H is an inverse of G
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
