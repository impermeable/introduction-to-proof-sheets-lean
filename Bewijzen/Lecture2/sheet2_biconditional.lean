import WaterproofGenre
import Verbose.English.All

open WaterproofGenre
open Verbose.NameLess

addAnonymousFactSplittingLemma LogicElims

#doc (WaterproofGenre) "Biconditional" =>

Now that we have discussed different strategies for conjunctions, disjunctions, and implications, we can also define new logical connectives, such as the biconditional operator (Definition 1.1.40).

The biconditional operator is represented by `A ⇔ B`. It is defined as two implications `A ⇒ B` and `B ⇒ A`.

If you have an assumption of this form, you can type `Since p ⇔ q we get that p ⇒ q and q ⇒ p`, and two implications will be added to your assumptions. From there, you can use other strategies to work with the assumption.

```lean
Example "1.1.41"
  Given: (p q : Prop)
  Assume:
  Conclusion: (p ⇔ q) ⇒ (q ⇒ p)
Proof:
  Assume that p ⇔ q
  Assume that q
  Since p ⇔ q we get that p ⇒ q and q ⇒ p
  Since q ⇒ p and q we conclude that p
QED
```

Proving a biconditional is similar to proving a conjunction. To prove `p ⇔ q` you provide two subproofs one for each of the implications `p ⇒ q` and `q ⇒ p`.

This is demonstrated in the following example.

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

Below is an exercise to practice working with biconditional operators.

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
