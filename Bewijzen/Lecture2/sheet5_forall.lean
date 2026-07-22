import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers
import Bewijzen.Customlib.Rational

open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting

addAnonymousGoalSplittingLemma rational_from_unannotated_sum
addAnonymousGoalSplittingLemma int_fraction_sum
addAnonymousGoalSplittingLemma rational_from_unannotated_comb
addAnonymousGoalSplittingLemma int_fractions_combine
addAnonymousGoalSplittingLemma rational_from_ints
addAnonymousGoalSplittingLemma rational_witnesses_int
addAnonymousGoalSplittingLemma rational_add
addAnonymousGoalSplittingLemma rational_of_eq
addAnonymousGoalSplittingLemma rational_of_two_mul
addAnonymousGoalSplittingLemma even_witnesses
addAnonymousGoalSplittingLemma even_of_two_mul
addAnonymousGoalSplittingLemma odd_of_two_mul_add_one
addAnonymousGoalSplittingLemma even_and_odd_false
addAnonymousGoalSplittingLemma even_not_odd
addAnonymousGoalSplittingLemma odd_not_even
addAnonymousGoalSplittingLemma not_even_odd
addAnonymousGoalSplittingLemma not_odd_even

#doc (WaterproofGenre) "For All" =>

The following pattern can be used to prove things about odd (or even).

:::hint "📦 Technical details"
```lean
configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em Int.even_or_odd
```
:::

```lean
Example "1.2.11"
  Given: (n : ℤ)
  Assume: (_ : n is odd)
  Conclusion: n * n is odd
Proof:
  Since n is odd we get k such that n = 2 * k + 1
  Fact: n * n =2 * (2 * k * k + 2 * k) + 1 by
    Calc
      n * n = (2 * k + 1) * (2 * k + 1) since n = 2 * k + 1
      _ = 2 * (2 * k *k + 2 * k) + 1 by computation
  Since n * n = 2 * (2 * k * k + 2 * k) + 1 we conclude that n * n is odd
QED
```

When there is a for-all quantifier in the goal, such as `∀ x : ℝ`, we can introduce an arbitrary variable using `Fix x`.
On paper, we write $`\forall x \in \mathbb{R}` instead of using the colon.

```lean
Example "1.2.13"
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, x ≤ 0 ∨ x ≥ 0
Proof:
  Fix x
  We discuss depending on whether x ≤ 0 or x > 0
  · Assume that x ≤ 0
    Let's prove that x ≤ 0
    · We conclude by hypothesis
  · Assume that x > 0
    Let's prove that x ≥ 0
    · Since x > 0 we conclude that x ≥ 0
QED
```
The first exercise is a trivial exercise, just to get used to the syntax. The second is a bit more involved.
::::multilean
```lean
Exercise "1.2.14"
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, x = x
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
  Given:
  Assume:
  Conclusion: ∀ n : ℤ, n is even ⇔ n * n is even
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

In Example 1.2.20, `P` is a proposition dependent on a real-valued variable. An example of a variable-dependent proposition from mathematics is `x^2 + x = 0`.
A statement `∀ x : ℝ, P x` means that the proposition `P x` holds for every `x : ℝ`.
To use a hypothesis `∀ x, P x`, write `Since ∀ x, P x we conclude that P a` for a specific `a`.

```lean
Example "1.2.20"
  Given: (P : ℝ → Prop)
  Assume: (_ : ∀ x : ℝ, P x)
  Conclusion: P 0
Proof:
  Since ∀ x : ℝ, P x we conclude that P 0
QED
```
Again, the first exercise is just to get used to the syntax, the next exercise is a bit more challenging.
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
  Conclusion: (∀ x : ℝ, P x ⇒ Q x) ⇒ ((∀ x : ℝ, P x) ⇒ ∀ x : ℝ, Q x)
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
  Given:
  Assume:
  Conclusion: ∀ x : ℝ, ∀ y : ℝ, x is irrational ⇒ ¬((x + y) is rational ∧ (x - y) is rational)
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
