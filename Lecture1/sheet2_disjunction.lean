import WaterproofGenre
import Verbose.English.All
open WaterproofGenre
open Verbose.NameLess
#doc (WaterproofGenre) "Disjunction" =>

```lean
Example "1.1.18left"
  Given: (p q r s : Prop)
  Assume: (_ : p) (_ : r)
  Conclusion: (p ∨ q) ∧ (r ∨ s)
Proof:
  Let's first prove that p ∨ q
  · Let's prove that p
    · We conclude by hypothesis
  Let's now prove that r ∨ s
  · Let's prove that r
    · We conclude by hypothesis
QED
```

::::multilean
```lean
Exercise "1.1.13_extra"
  Given: (p q r : Prop)
  Assume: (_ : p)
  Conclusion: (p ∨ q) ∨ r
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
Example "1.1.20"
  Given: (p q r : Prop)
  Assume: (_ : (p ∨ q) ∧ r)
  Conclusion: p ∨ (q ∧ r)
Proof:
  Since (p ∨ q) ∧ r we get that p ∨ q and r
  We discuss depending on whether p or q
  · Assume that p
    Let's prove that p
    · We conclude by hypothesis
  · Assume that q
    Let's prove that q ∧ r
    · Since q and r we conclude that q ∧ r
QED
```

::::multilean
```lean
Exercise "1.1.21"
  Given: (p q r : Prop)
  Assume: (_ : q ∨ r)
  Conclusion: (p ∨ q) ∨ (p ∨ r)
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
