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
noncomputable def f : ℝ → ℝ := fun x => (2 * x + 1) / 3

-- The specific function used in Exercise 3.2.39b
def g : Set ℕ → Set ℕ := fun A => Aᶜ

#doc (WaterproofGenre) "Inverse Functions" =>

A function `g` is a left inverse of `f : X → Y` when `∀ x : X, g(f(x)) = x`,
and a right inverse when `∀ y : Y, f(g(y)) = y`. We say `g` is an inverse of
`f` when it is both, and you can use that `g is an inverse of f` means
`g is a left inverse of f ∧ g is a right inverse of f`.

```lean
Example "Left inverse of the identity"
  Given:
  Assume:
  Conclusion: ∃ g : ℝ → ℝ, g is a left inverse of id
Proof:
  Let's prove that id works
  It suffices to prove that ∀ x : ℝ, id(id(x)) = x
  Fix x
  We compute
QED
```

::::multilean
```lean
Exercise "3.2.25"
  Given: (X Y : Type) (f : X → Y)
  Assume: (_ : f has a left inverse)
  Conclusion: f is injective
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

`f : ℝ → ℝ` is the function `f x = (2 * x + 1) / 3`


::::multilean
```lean
Exercise "3.2.39a"
  Given:
  Assume:
  Conclusion: ∃ g : ℝ → ℝ, g is an inverse of f
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

`g : Set ℕ → Set ℕ` is the function `g A = Aᶜ`.

::::multilean
```lean
Exercise "3.2.39b"
  Given:
  Assume:
  Conclusion: ∃ h : Set ℕ → Set ℕ, h is an inverse of g
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
