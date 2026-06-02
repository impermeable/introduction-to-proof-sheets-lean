import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers
import Bewijzen.Customlib.Rational

open WaterproofGenre
open Verbose.NameLess

addAnonymousGoalSplittingLemma rational_add
addAnonymousGoalSplittingLemma rational_of_eq
addAnonymousGoalSplittingLemma rational_of_two_mul
addAnonymousGoalSplittingLemma even_witnesses
addAnonymousGoalSplittingLemma even_of_two_mul
addAnonymousGoalSplittingLemma odd_of_two_mul_add_one
addAnonymousGoalSplittingLemma even_and_odd_false

#doc (WaterproofGenre) "For All" =>

A statement `∀ x, P x` means that `P x` holds for every `x`.
To prove such a statement, use `Fix x` to introduce an arbitrary element, then prove `P x`.
To use a hypothesis `∀ x, P x`, write `Since ∀ x, P x we conclude that P a` for a specific `a`.

```lean
configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em Int.even_or_odd
```



```lean
Example "1.2.11"
  Given: (n : ℤ)
  Assume: (_ : n is odd)
  Conclusion: n * n is odd
Proof:
  Since n is odd we get k such that n = 2 * k + 1
  Since n = 2 * k + 1 we get that n * n = 2 * (2 * k * k + 2 * k) + 1
  Since n * n = 2 * (2 * k * k + 2 * k) + 1 we conclude that n * n is odd
QED
```

```lean
Example "1.2.13"
  Given: (x : ℝ)
  Assume:
  Conclusion: x ≤ 0 ∨ x ≥ 0
Proof:
  We discuss depending on whether x ≤ 0 or x > 0
  · Assume that x ≤ 0
    Let's prove that x ≤ 0
    · We conclude by hypothesis
  · Assume that x > 0
    Let's prove that x ≥ 0
    · Since x > 0 we conclude that x ≥ 0
QED
```

::::multilean
```lean
Exercise "1.2.14"
  Given: (x : ℝ)
  Assume:
  Conclusion: x = x
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
Exercise "1.2.15"
  Given: (n : ℤ)
  Assume:
  Conclusion: n is even ⇔ n * n is even
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
Example "1.2.20"
  Given: (P : ℝ → Prop)
  Assume: (_ : ∀ x : ℝ, P x)
  Conclusion: P 0
Proof:
  Since ∀ x : ℝ, P x we conclude that P 0
QED
```

::::multilean
```lean
Exercise "1.2.21"
  Given: (P : ℝ → Prop)
  Assume: (_ : ∀ x : ℝ, P x)
  Conclusion: P 21
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
Exercise "1.2.22"
  Given: (P Q : ℝ → Prop)
  Assume:
  Conclusion: (∀ x : ℝ, P x ⇒ Q x) ⇒ (∀ x : ℝ, P x) ⇒ ∀ x : ℝ, Q x
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

Below is an exercise involving irrational numbers.

::::multilean
```lean
Exercise "1.2.18"
  Given: (x y : ℝ)
  Assume: (_ : x is irrational)
  Conclusion: ¬((x + y) is rational ∧ (x - y) is rational)
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
