import WaterproofGenre
import Verbose.English.All

open WaterproofGenre

#doc (WaterproofGenre) "Biconditional" =>

```lean
Example "1.1.41"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇔ q) ⇒ q ⇒ p
Proof:
  Assume that p ⇔ q
  Assume that q
  Since p ⇔ q we get that p ⇒ q and q ⇒ p
  Since q ⇒ p and q we conclude that p
QED
```

```lean
Example "1.1.42"
  Given: (p q : Prop)
  Assume:
  Conclusion: p ⇒ q ⇒ (p ⇔ q)
Proof:
  Assume that p
  Assume that q
  Let's first prove that p ⇒ q
  · Assume that p
    We conclude by hypothesis
  Let's now prove that q ⇒ p
  · Assume that q
    We conclude by hypothesis
QED
```


::::multilean
```lean
Exercise "1.1.43"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇔ q) ⇔ (q ⇔ p)
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
