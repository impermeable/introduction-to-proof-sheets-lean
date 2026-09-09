import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers


open WaterproofGenre
open Verbose.NameLess

addAnonymousGoalSplittingLemma expand_cube_succ

#doc (WaterproofGenre) "Exists" =>

# Existential quantification (∃)

## How to prove ∃-goal

Example 1.2.25 below shows how you can prove an existentially quantified statement.
To prove such a statement, use `Let's prove that a works` for a specific `a`, then prove `P a`.

```lean
Example "1.2.25"
  Given:
  Assume:
  Conclusion: ∃ n : ℤ, (∃ k : ℤ, k * k = n) ∧ (∃ l : ℤ, l * l * l + 1 = n)
Proof:
  Let's prove that 9 works
  Let's first prove that ∃ k : ℤ, k * k = 9
  · Let's prove that 3 works
    We compute
  Let's now prove that ∃ l : ℤ, l * l * l + 1 = 9
  · Let's prove that 2 works
    We compute
QED
```

```lean
Example "1.2.26"
  Given: (a : ℝ)
  Assume:
  Conclusion: ∃ x : ℝ, x * x * x + (1 - a ^ 2) * x - a = 0
Proof:
  Let's prove that a works: a * a * a + (1 - a ^ 2) * a - a = 0
  We compute
QED
```

In Waterproof, the notation `a ∣ b` for integers `a` and `b` means that `∃ m : ℤ, b = a * m`.
Use this to prove the following fact.

(the notation `∣` is written using `\abs`, not the `|`-symbol on your keyboard!)

::::multilean
```lean
Exercise "1.2.28"
  Given:
  Assume:
  Conclusion: ∃ n : ℤ, 0 ∣ n
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

## How to use an ∃-assumption

To use a hypothesis `∃ x, P x`, write `Since ∃ x, P x we get x such that P x`.

In the example below, we write `It suffices to prove that ...` to transform the goal from a divisibility expression to the form with an existential quantifier.



```lean
Example "1.2.31"
  Given: (n : ℤ)
  Assume: (_ : 3 ∣ n ^ 3)
  Conclusion: 3 ∣ (n + 1) ^ 3 - 1
Proof:
  Since 3 ∣ n ^ 3 we get that ∃ q : ℤ, n ^ 3 = 3 * q
  Since ∃ q : ℤ, n ^ 3 = 3 * q we get q such that n ^ 3 = 3 * q
  It suffices to prove that ∃ k : ℤ, (n + 1) ^ 3 - 1 = 3 * k
  Let's prove that q + n ^ 2 + n works
  Since n ^ 3 = 3 * q we conclude that (n + 1) ^ 3 - 1 = 3 * (q + n ^ 2 + n)
QED
```



