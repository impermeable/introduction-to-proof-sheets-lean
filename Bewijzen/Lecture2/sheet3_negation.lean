import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Rational

open WaterproofGenre
open Verbose.NameLess

addAnonymousGoalSplittingLemma rational_witnesses_int
addAnonymousGoalSplittingLemma rational_from_ints
addAnonymousGoalSplittingLemma eq_neg_frac_of_neg_eq_frac
addAnonymousGoalSplittingLemma rational_from_neg_cast_frac
addAnonymousGoalSplittingLemma rational_of_neg_int_frac
addAnonymousGoalSplittingLemma ne_zero_of_recip_frac
addAnonymousGoalSplittingLemma eq_of_recip_frac

#doc (WaterproofGenre) "Negation" =>

Negation is defined as follows: `¬A` means `A ⇒ False`.

To prove a negation, use `Assume that A` and then prove a contradiction.
To derive a contradiction, first write `It suffices to prove that False` and then conclude `False` from the contradicting hypotheses.

```lean
Example "1.1.54"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇒ q) ⇒ ¬q ⇒ ¬p
Proof:
  Assume that p ⇒ q
  Assume that ¬q
  Assume that p
  Since p ⇒ q and p we get that q
  It suffices to prove that False
  Since ¬q and q we conclude that False
QED
```

::::multilean
```lean
Exercise "1.1.56"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇒ ¬q) ⇒ q ⇒ ¬p
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
Exercise "1.1.57"
  Given: (p q : Prop)
  Assume:
  Conclusion: ¬p ⇒ ¬q ⇒ ¬(p ∨ q)
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

Below are exercises involving irrational numbers. Recall that a real number is irrational if it is not rational.

::::multilean
```lean
Exercise "1.1.58a"
  Given: (x : ℝ)
  Assume:
  Conclusion: x is irrational ⇒ -x is irrational
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
Exercise "1.1.58b"
  Given: (x : ℝ)
  Assume:
  Conclusion: x ≠ 0 ⇒ x is irrational ⇒ 1 / x is irrational
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
