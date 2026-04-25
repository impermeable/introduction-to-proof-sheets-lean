import WaterproofGenre
import Verbose.English.All


open WaterproofGenre
open Verbose.NameLess

#doc (WaterproofGenre) "Conjunction" =>

::::multilean
```lean
Example "1.1.1"
  Given: (a b c : ℤ)
  Assume: (_ : c ∣ b) (_ : b ∣ a)
  Conclusion: c ∣ a
Proof:
  Since c ∣ b we get n such that b = c * n
  Since b ∣ a we get m such that a = b * m
  Let's prove that n * m works
  Since b = c * n and a = b * m we conclude that a = c * (n * m)
QED
```
::::

```lean
Example "1.1.8"
  Given: (p q r : Prop)
  Assume: (_ : p) (_ : q) (_ : r)
  Conclusion: (p ∧ q) ∧ r
Proof:
  Let's first prove that p ∧ q
  · Let's first prove that p
    · We conclude by hypothesis
    Let's now prove that q
    · We conclude by hypothesis
  Let's now prove that r
  · We conclude by hypothesis
QED
```

```lean
Example "1.1.11"
  Given: (p q : Prop)
  Assume: (_ : p ∧ q)
  Conclusion: q ∧ p
Proof:
  Since p ∧ q we get that p and q
  Let's first prove that q
  · We conclude by hypothesis
  Let's now prove that p
  · We conclude by hypothesis
QED
```

::::multilean
```lean
Exercise "1.1.13"
  Given: (p q r : Prop)
  Assume: (_ : (p ∧ q) ∧ r)
  Conclusion: q
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
Exercise "1.1.14"
  Given: (p q r s : Prop)
  Assume: (_ : p) (_ : q) (_ : r) (_ : s)
  Conclusion: (p ∧ q) ∧ (r ∧ s)
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
