import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers

open WaterproofGenre

#doc (WaterproofGenre) "Quantifier Alternation" =>

When quantifiers alternate (e.g., `∃ y, ∀ x, ...` versus `∀ x, ∃ y, ...`), the order matters.
In general, `∃ y, ∀ x, P x y` implies `∀ x, ∃ y, P x y`, but not the other way around.

```lean
configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em Int.even_or_odd

addAnonymousGoalSplittingLemma even_add_even
addAnonymousGoalSplittingLemma odd_add_odd
addAnonymousGoalSplittingLemma even_add_odd
addAnonymousGoalSplittingLemma odd_add_even
addAnonymousGoalSplittingLemma even_and_odd_false
```

::::multilean
```lean
Exercise "1.2.39a"
  Given:
  Assume:
  Conclusion: ∀ x : ℤ, ∃ y : ℤ, x + y is even
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
Exercise "1.2.39b"
  Given:
  Assume:
  Conclusion: ¬(∃ y : ℤ, ∀ x : ℤ, (x + y) is even)
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
Example "1.2.40"
  Given: (X Y : Type) (p : X → Y → Prop)
  Assume:
  Conclusion: (∃ y : Y, ∀ x : X, p x y) ⇒ ∀ x : X, ∃ y : Y, p x y
Proof:
  Assume that ∃ y : Y, ∀ x : X, p x y
  Since ∃ y : Y, ∀ x : X, p x y we get b such that ∀ x : X, p x b
  Fix a
  Let's prove that b works
  Since ∀ x : X, p x b we conclude that p a b
QED
```
