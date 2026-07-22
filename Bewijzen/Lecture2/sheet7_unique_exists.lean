import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists

open Verbose.NameLess
open Verbose.Contradicting
open WaterproofGenre

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le caseSplittingClassical
addAnonymousGoalSplittingLemma squareRoot
addAnonymousGoalSplittingLemma add_pos

#doc (WaterproofGenre) "Unique Existence" =>

A statement `∃! x, P x` means there exists a unique `x` for which `P x` holds.
To prove it, use `Let's prove that a works`, then prove `P a`, and then prove `∀ y, P y ⇒ y = a`.
Note that this is different from the book, where this is given as an alternative characterisation.
We will prove the reverse characterisation provided in the book, and then use the alternative charactisation by default.

```lean
Example "1.2.38_alternative"
  Given: (X : Type) (P : X → Prop)
  Assume:
  Conclusion: (∃! x : X, P x) ⇔ ((∃ x : X, P x) ∧ ∀ x y : X, P x ∧ P y ⇒ x = y)
Proof:
  Let's first prove that (∃! x : X, P x) ⇒ (∃ x : X, P x) ∧ ∀ x y : X, P x ∧ P y ⇒ x = y
  · Assume that ∃! x : X, P x
    Since ∃! x : X, P x we get c such that P c and ∀ y : X, P y ⇒ y = c
    Let's first prove that ∃ x, P x
    · Let's prove that c works
      We conclude by hypothesis
    Let's now prove that ∀ x y : X, P x ∧ P y ⇒ x = y
    · Fix x
      Fix y
      Assume that P x ∧ P y
      Since ∀ y : X, P y ⇒ y = c, P x and P y we get that y = c and x = c
      Since y = c and x = c we conclude that x = y
  Let's now prove that ((∃ x : X, P x) ∧ ∀ x y : X, P x ∧ P y ⇒ x = y) ⇒ ∃! x : X, P x
  · Assume that (∃ x : X, P x) ∧ ∀ x y : X, P x ∧ P y ⇒ x = y
    Since (∃ x : X, P x) ∧ ∀ x y : X, P x ∧ P y ⇒ x = y we get c such that P c
    Let's prove that c works
    Let's first prove that P c
    · We conclude by hypothesis
    Let's now prove that ∀ y : X, P y ⇒ y = c
    · Fix y
      Assume that P y
      Since ∀ x y : X, P x ∧ P y ⇒ x = y, P c and P y we conclude that y = c
QED
```

```lean
Example "1.2.36"
  Given: (a : ℝ)
  Assume:
  Conclusion: a > 0 ⇒ ∃! b : ℝ, b > 0 ∧ b ^ 2 = a
Proof:
  Assume that a > 0
  Let's prove that √a works
  Let's first prove that √a > 0 ∧ √a ^ 2 = a
  · Since a > 0 we conclude that √a > 0 ∧ √a ^ 2 = a
  Let's now prove that ∀ y : ℝ, y > 0 ∧ y ^ 2 = a ⇒ y = √a
  · Fix y
    Assume that y > 0 ∧ y ^ 2 = a
    Since y > 0 ∧ y ^ 2 = a we get that y > 0 and y ^ 2 = a
    Since a > 0 we get that √a > 0 ∧ √a ^ 2 = a
    Since √a > 0 ∧ √a ^ 2 = a we get that √a > 0 and √a ^ 2 = a
    Fact: (y + √a) * (y - √a) = 0 by
      Calc
        (y + √a) * (y - √a) = y ^ 2 - √a ^ 2 by computation
        _ = a - a since y ^ 2 = a and √a ^ 2 = a
        _ = 0 by computation
    Since (y + √a) * (y - √a) = 0 we get that y + √a = 0 ∨ y - √a = 0
    We discuss depending on whether y + √a = 0 or y - √a = 0
    · Assume that y + √a = 0
      Let's prove it's contradictory
      Since y > 0 and √a > 0 we get that y + √a > 0
      We conclude by contradicting y + √a = 0 and y + √a > 0
    · Assume that y - √a = 0
      Since y - √a = 0 we conclude that y = √a
QED
```

Two exercises to practice proving unique existence.

::::multilean
```lean
Exercise "1.2.37a"
  Given: (a : ℝ)
  Assume:
  Conclusion: ∃! x : ℝ, x ^ 2 + 2 * a * x + a ^ 2 = 0
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
Exercise "1.2.37b"
  Given:
  Assume:
  Conclusion: ∃! a : ℝ, ∃ x : ℝ, x ^ 2 + a ^ 2 = 0
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
