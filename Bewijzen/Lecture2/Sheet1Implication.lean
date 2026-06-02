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

#doc (WaterproofGenre) "Implication" =>

```lean
Example "1.1.29"
  Given: (p q : Prop)
  Assume:
  Conclusion: p ⇒ q ⇒ p
Proof:
  Assume that p
  Assume that q
  We conclude by hypothesis
QED
```


```lean
Example "1.1.23"
  Given: (x y : ℝ)
  Assume:
  Conclusion: x is rational ⇒ x + y is rational ⇒ y is rational
Proof:
  Assume that x is rational
  Assume that x + y is rational
  Since x is rational we get n : ℤ and d : ℤ such that d ≠ 0 and x = n / d
  Since x + y is rational we get m : ℤ and e : ℤ such that e ≠ 0 and x + y = m / e
  Let's prove that y is rational
  Since x + y = m / e and x = n / d we get that y = m / e - n / d
  Since y = m / e - n / d, e ≠ 0 and d ≠ 0 we get that y = (m * d - n * e) / (e * d)
  Since e ≠ 0 and d ≠ 0 we get that e * d ≠ 0
  Since e * d ≠ 0 and y = (m * d - n * e) / (e * d) we conclude that y is rational
QED
```


::::multilean
```lean
Exercise "1.1.32"
  Given: (r s : Prop)
  Assume:
  Conclusion: r ⇒ s ⇒ s
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
  Conclusion: a ∨ b ⇒ c ⇒ (c ∧ a) ∨ b
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


::::multilean
```lean
Exercise "1.1.37"
  Given: (p q r : Prop)
  Assume:
  Conclusion: (p ⇒ q ⇒ r) ⇒ q ⇒ p ⇒ r
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
  Conclusion: (p ⇒ p ∧ q) ⇒ p ∨ q ⇒ q
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
