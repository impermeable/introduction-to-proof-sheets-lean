import WaterproofGenre
import Bewijzen.Customlib.Reals

open WaterproofGenre

#doc (WaterproofGenre) "Unique Existence" =>

A statement `∃! x, P x` means there exists a unique `x` for which `P x` holds.
To prove it, use `Let's prove that a works`, then prove `P a`, and then prove `∀ y, P y → y = a`.

```lean
configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em
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
    Since y > 0, a > 0 and y ^ 2 = a we conclude that y = √a
QED
```

```lean
Example "1.2.38"
  Given: (P : ℝ → Prop)
  Assume:
  Conclusion: (∃! x : ℝ, P x) ↔ (∃ x : ℝ, P x ∧ ∀ y : ℝ, P y ⇒ y = x)
Proof:
  Let's first prove that (∃! x, P x) ⇒ ∃ x, P x ∧ ∀ y, P y ⇒ y = x
  · Assume that ∃! x, P x
    We conclude by hypothesis
  Let's now prove that (∃ x, P x ∧ ∀ y, P y ⇒ y = x) ⇒ ∃! x, P x
  · Assume that ∃ x, P x ∧ ∀ y, P y ⇒ y = x
    We conclude by hypothesis
QED
```

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
