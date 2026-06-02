import WaterproofGenre
import Verbose.English.All
open WaterproofGenre
open Verbose.NameLess
#doc (WaterproofGenre) "Disjunction" =>

Proving disjunctions (1.1.15) uses a similar phrase `Let's prove that [statement]` to proving conjunctions (1.1.7), but without `first` and `next` keyword and, in contrast to conjunctions, just one of the two proposition has to be proven.

To prove disjunctions we type `Let's prove that [statement]`, specifying either the left or right proposition, then demonstrate the proof of the chosen proposition.

```lean
Example "1.1.18left"
  Given: (p q r s : Prop)
  Assume: (_ : p) (_ : r)
  Conclusion: (p ∨ q) ∧ (r ∨ s)
Proof:
  Let's first prove that p ∨ q
  · Let's prove that p
    · We conclude by hypothesis
  Let's now prove that r ∨ s
  · Let's prove that r
    · We conclude by hypothesis
QED
```

Do the exercise below to practice proving disjunctions (1.1.16). This exercise is not in the book.

::::multilean
```lean
Exercise "1.1.13_extra"
  Given: (p q r : Prop)
  Assume: (_ : p)
  Conclusion: (p ∨ q) ∨ r
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

Below is an example of assuming disjunctions (proof by cases, Strategy 1.1.19).
This is done by using `We discuss depending on whether [statement] or [statement]`, followed by two subproofs where the left and right propositions are assumed respectively, using `Assume that [statement]`.

```lean
Example "1.1.20"
  Given: (p q r : Prop)
  Assume: (_ : (p ∨ q) ∧ r)
  Conclusion: p ∨ (q ∧ r)
Proof:
  Since (p ∨ q) ∧ r we get that p ∨ q and r
  We discuss depending on whether p or q
  · Assume that p
    Let's prove that p
    · We conclude by hypothesis
  · Assume that q
    Let's prove that q ∧ r
    · Since q and r we conclude that q ∧ r
QED
```

Do the exercise below to practice using proof by cases.

::::multilean
```lean
Exercise "1.1.21"
  Given: (p q r : Prop)
  Assume: (_ : q ∨ r)
  Conclusion: (p ∨ q) ∨ (p ∨ r)
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
