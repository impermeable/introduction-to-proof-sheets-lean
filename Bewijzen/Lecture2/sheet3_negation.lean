import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Rational

open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting

addAnonymousGoalSplittingLemma rational_witnesses_int
addAnonymousGoalSplittingLemma rational_from_ints
addAnonymousGoalSplittingLemma eq_neg_frac_of_neg_eq_frac
addAnonymousGoalSplittingLemma rational_from_neg_cast_frac
addAnonymousGoalSplittingLemma rational_of_neg_int_frac
addAnonymousGoalSplittingLemma ne_zero_of_recip_frac
addAnonymousGoalSplittingLemma eq_of_recip_frac

#doc (WaterproofGenre) "Negation" =>

Negation is defined as follows: `¬p` means `p ⇒ False`.

To prove a negation, you can use `Assume that q` and then prove a contradiction.

In Waterproof, to prove a contradiction, you need assumptions that contradict each other, and then type `We conclude by contradicting ¬q and q`.

An example is shown below.

```lean
Example "1.1.54"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇒ q) ⇒ (¬q ⇒ ¬p)
Proof:
  Assume that p ⇒ q and ¬q
  Assume that p
  Since p ⇒ q and p we get that q
  We conclude by contradicting ¬q and q
QED
```

Below are two exercises using negations.

::::multilean
```lean
Exercise "1.1.56"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇒ ¬q) ⇒ (q ⇒ ¬p)
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
  Conclusion: ¬p ⇒ (¬q ⇒ ¬(p ∨ q))
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

Below are exercises involving irrational numbers and proof by contradiction.
Remember that a real number is irrational if it is not rational.

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
  Conclusion: x ≠ 0 ⇒ (x is irrational ⇒ 1 / x is irrational)
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
