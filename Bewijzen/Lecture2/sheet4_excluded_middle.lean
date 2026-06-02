import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Integers

open WaterproofGenre

addAnonymousGoalSplittingLemma odd_of_two_mul_add_one
addAnonymousGoalSplittingLemma even_and_odd_false

#doc (WaterproofGenre) "Excluded Middle" =>

The law of excluded middle states that for any proposition `p`, either `p` or `¬p` holds.
In Lean Verbose, you can use `We discuss depending on whether p or ¬ p` to split into cases.

```lean
configureAnonymousCaseSplittingLemmas Classical.em Int.even_or_odd
```

```lean
Example "1.1.64"
  Given: (p q : Prop)
  Assume: (_ : ¬(p ∧ q))
  Conclusion: ¬p ∨ ¬q
Proof:
  We discuss depending on whether p or ¬ p
  · Assume that p
    We discuss depending on whether q or ¬ q
    · Assume that q
      Let's prove it's contradictory
      Since p and q we get that p ∧ q
      It suffices to prove that False
      Since ¬(p ∧ q) and p ∧ q we conclude that False
    · Assume that ¬q
      Let's prove that ¬q
      · We conclude by hypothesis
  · Assume that ¬p
    Let's prove that ¬p
    · We conclude by hypothesis
QED
```

::::multilean
```lean
Exercise "1.1.67"
  Given: (p q : Prop)
  Assume:
  Conclusion: (¬q ⇒ ¬p) ⇒ p ⇒ q
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

Proposition 1.1.65 is an example of use of the law of excluded middle.

```lean
Example "1.1.65"
  Given: (a b : ℤ)
  Assume:
  Conclusion: (a * b) is even ⇒ a is even ∨ b is even
Proof:
  Assume that (a * b) is even
  We discuss depending on whether a is even or a is odd
  · Assume that a is even
    Let's prove that a is even
    · We conclude by hypothesis
  · Assume that a is odd
    We discuss depending on whether b is even or b is odd
    · Assume that b is even
      Let's prove that b is even
      · We conclude by hypothesis
    · Assume that b is odd
      Let's prove it's contradictory
      Since a is odd we get k such that a = 2 * k + 1
      Since b is odd we get l such that b = 2 * l + 1
      Since a = 2 * k + 1 and b = 2 * l + 1 we get that a * b = 2 * (2 * k * l + k + l) + 1
      Since a * b = 2 * (2 * k * l + k + l) + 1 we get that a * b is odd
      Since a * b is even we get that ¬(a * b is odd)
      It suffices to prove that False
      Since ¬(a * b is odd) and a * b is odd we conclude that False
QED
```
