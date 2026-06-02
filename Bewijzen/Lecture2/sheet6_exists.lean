import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers


open WaterproofGenre
addAnonymousGoalSplittingLemma expand_cube_succ
#doc (WaterproofGenre) "Exists" =>

A statement `∃ x, P x` means that there exists some `x` for which `P x` holds.
To prove such a statement, use `Let's prove that a works` for a specific `a`, then prove `P a`.
To use a hypothesis `∃ x, P x`, write `Since ∃ x, P x we get x such that P x`.

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

```lean
Example "1.2.31"
  Given: (n : ℤ)
  Assume: (_ : 3 ∣ n ^ 3)
  Conclusion: 3 ∣ (n + 1) ^ 3 - 1
Proof:
  Since 3 ∣ n ^ 3 we get m such that n ^ 3 = 3 * m
  It suffices to prove that ∃ k : ℤ, (n + 1) ^ 3 - 1 = 3 * k
  Let's prove that m + n ^ 2 + n works
  Since n ^ 3 = 3 * m we conclude that (n + 1) ^ 3 - 1 = 3 * (m + n ^ 2 + n)
QED
```
