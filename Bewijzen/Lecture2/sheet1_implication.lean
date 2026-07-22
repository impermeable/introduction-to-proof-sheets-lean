import WaterproofGenre
import Verbose.English.All
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Bewijzen.Customlib.Rational

open WaterproofGenre
open Verbose.NameLess


addAnonymousGoalSplittingLemma rational_from_unannotated_comb
addAnonymousGoalSplittingLemma mul_ne_zero
addAnonymousGoalSplittingLemma int_fractions_combine
addAnonymousGoalSplittingLemma rational_from_ints
addAnonymousGoalSplittingLemma rational_witnesses_int

set_option linter.unusedTactic false

#doc (WaterproofGenre) "Implication" =>

Below is an example of proving implications (Strategy 1.1.28).
You type `Assume that [statement]` to assume the left-hand side of an implication.
When the goal is a chain of implications, you can assume several statements at once by separating them with `and` or commas, for example `Assume that p and q`.

```lean
Example "1.1.29"
  Given: (p q : Prop)
  Assume:
  Conclusion: p ⇒ (q ⇒ p)
Proof:
  Assume that p
  Assume that q
  We conclude by hypothesis
QED
```

Below is another example of proving implications (Strategy 1.1.28).
This example involves rational numbers, defined as follows:

`x is rational` holds if there exist `n : ℤ, d : ℤ such that d ≠ 0 and x = n/d`.

This definition means that a number is rational if it can be written as a fraction of two integers, where the denominator is not zero (since division by zero is undefined).

Thus, if you know that `x` is rational, there exist integers `n` and `d` such that `d ≠ 0` and `x = n/d`. To prove that `x` is rational, it is sufficient to have both `d ≠ 0` and `x = n/d` in your assumptions for some fixed `n` and `d`.

```lean
Example "1.1.23"
  Given: (x y : ℝ)
  Assume:
  Conclusion: x is rational ⇒ (x + y is rational ⇒ y is rational)
Proof:
  Assume that x is rational
  Assume that x + y is rational
  Since x is rational we get n : ℤ and d : ℤ such that d ≠ 0 and x = n / d
  Since x + y is rational we get m : ℤ and e : ℤ such that e ≠ 0 and x + y = m / e
  Let's prove that y is rational
  Fact: y = (m * d - n * e) / (e * d) by
    Calc
      y = (x + y) - x by computation
      _ = m/e - x since x + y = m/e
      _ = m/e - n/d since x = n/d
      _ = (m * d - n * e) / (e * d) since e ≠ 0 and d ≠ 0
  Since e ≠ 0 and d ≠ 0 we get that e * d ≠ 0
  Since e * d ≠ 0 and y = (m * d - n * e) / (e * d) we conclude that y is rational
QED
```

Below are two exercises to practice proving implications (Strategy 1.1.28).

::::multilean
```lean
Exercise "1.1.32"
  Given: (r s : Prop)
  Assume:
  Conclusion: r ⇒ (s ⇒ s)
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
Exercise "1.1.33"
  Given: (a b c : Prop)
  Assume:
  Conclusion: a ∨ b ⇒ (c ⇒ (c ∧ a) ∨ b)
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

Below is an example of assuming implications (modus ponens, Strategy 1.1.34).

We type `Since (p ∨ q) ⇒ r it suffices to prove that p ∨ q` to perform backwards reasoning. When the goal is `r` and we have the implication `(p ∨ q) ⇒ r` in our assumptions, it is enough to show `p ∨ q`, so we make it our new goal.

```lean
Example "1.1.35"
  Given: (p q r : Prop)
  Assume:
  Conclusion: ((p ∨ q) ⇒ r) ∧ p ⇒ r
Proof:
  Assume that ((p ∨ q) ⇒ r) ∧ p
  Since ((p ∨ q) ⇒ r) ∧ p we get that (p ∨ q) ⇒ r and p
  Since (p ∨ q) ⇒ r it suffices to prove that p ∨ q
  Let's prove that p
  We conclude by hypothesis
QED
```

Below is an alternative proof using direct reasoning.

We type `Fact: [statement] by` to define a proposition as a new assumption, after which we provide a proof of it.

```lean
-- alternative direct proof
Example "1.1.35"
  Given: (p q r : Prop)
  Assume:
  Conclusion: ((p ∨ q) ⇒ r) ∧ p ⇒ r
Proof:
  Assume that ((p ∨ q) ⇒ r) ∧ p
  Since ((p ∨ q) ⇒ r) ∧ p we get that (p ∨ q) ⇒ r and p
  Fact: p ∨ q by
    · Let's prove that p
      · We conclude by hypothesis
  Since (p ∨ q) ⇒ r and p ∨ q we conclude that r
QED
```

Below are two exercises that require assuming implications (Strategy 1.1.34).

::::multilean
```lean
Exercise "1.1.37"
  Given: (p q r : Prop)
  Assume:
  Conclusion: (p ⇒ (q ⇒ r)) ⇒ (q ⇒ (p ⇒ r))
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
Exercise "1.1.38"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇒ p ∧ q) ⇒ (p ∨ q ⇒ q)
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
