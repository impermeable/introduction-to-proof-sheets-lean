import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Rational
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess

addAnonymousGoalSplittingLemma orderAntisymmetry
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma rationalArithmetic

#doc (WaterproofGenre) "Relations" =>

This exercise sheet is for Section 5.1 Relations from the book Infinite Descent
into Mathematics. It covers two properties a relation can have: antisymmetry and
transitivity.

A relation on a set `X` is written as a function of two arguments, so the
relation `≤` on `ℝ` is written `fun a b : ℝ => a ≤ b`.

# Antisymmetry

A relation `R` is *antisymmetric* when any two elements that are related in both
directions are equal. In Waterproof, `R is antisymmetric` means by definition
that `∀ a b : X, R a b → R b a → a = b`. To prove a relation is antisymmetric you
start with `Fix a b` to introduce the two elements, and then `Assume that ...`
for each of the two directions.

```lean
Example "5.1.32"
  Given:
  Assume:
  Conclusion: (fun a b : ℝ => a ≤ b) is antisymmetric
Proof:
  Fix a b
  Assume that a ≤ b
  Assume that b ≤ a
  Since a ≤ b and b ≤ a we conclude that a = b
QED
```

In the exercise below we use `Set Z` as notation for `𝒫(Z)`, the powerset of `Z`.
::::multilean
```lean
Exercise "5.1.34"
  Given: (Z : Type)
  Assume:
  Conclusion: (fun A B : Set Z => A ⊆ B) is antisymmetric
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

# Transitivity

A relation `R` is *transitive* when relations chain: `R is transitive` means by
definition that `∀ a b c : X, R a b → R b c → R a c`. As with antisymmetry, you
start the proof with `Fix a b c` and then `Assume that ...` for each of the two
hypotheses.

In the example below, `(b - a) is rational` states that the difference of `b` and
`a` is a rational number. The proof uses that a sum of two rational numbers is
again rational, and then uses the computation
`(c - b) + (b - a) = c - a`. 

```lean
Example "5.1.38"
  Given:
  Assume:
  Conclusion: (fun a b : ℝ => (b - a) is rational) is transitive
Proof:
  Fix a b c
  Assume that (b - a) is rational
  Assume that (c - b) is rational
  Since (c - b) is rational and (b - a) is rational 
    we get that (c - b) + (b - a) is rational
  Since (c - b) + (b - a) is rational and (c - b) + (b - a) = c - a 
    we conclude that (c - a) is rational
QED
```

In the exercise below you can practice with proving transitivity.

::::multilean
```lean
Exercise "5.1.39"
  Given: (Z : Type)
  Assume:
  Conclusion: (fun A B : Set Z => A ⊆ B) is transitive
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
