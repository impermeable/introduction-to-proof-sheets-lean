import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Lists

open WaterproofGenre
open Verbose.NameLess
open Verbose.Contradicting
open scoped Bewijzen.IntervalNotation
open scoped Bewijzen.PairSetNotation

configureAnonymousCaseSplittingLemmas caseSplittingClassical caseSplittingRealDichotomies
addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderTheory
addAnonymousGoalSplittingLemma intervalMembership
addAnonymousGoalSplittingLemma deMorgan
addAnonymousGoalSplittingLemma realSignArithmetic
addAnonymousGoalSplittingLemma pairSets
addAnonymousGoalSplittingLemma Or.symm


#doc (WaterproofGenre) "Double Containment" =>

Below is a lemma that is not in the book, but is used in the proof of Example 2.1.16.

```lean
Lemma multiplication_dichotomy "multiplication_dichotomy"
  Given: (a b : ℝ)
  Assume: (_ : a * b ≥ 0)
  Conclusion: (a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0)
Proof:
  We discuss depending on whether a ≥ 0 or a ≤ 0
  · Assume that a ≥ 0
    We discuss depending on whether b ≥ 0 or b ≤ 0
    · Assume that b ≥ 0
      Let's prove that a ≥ 0 ∧ b ≥ 0
      · Since a ≥ 0 and b ≥ 0 we conclude that a ≥ 0 ∧ b ≥ 0
    · Assume that b ≤ 0
      Assume for contradiction that ¬ ((a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0))
      Since ¬ ((a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0)) we get that (a < 0 ∨ b < 0) ∧ (a > 0 ∨ b > 0)
      We conclude by contradicting (a < 0 ∨ b < 0) ∧ (a > 0 ∨ b > 0) and a * b ≥ 0
  · Assume that a ≤ 0
    We discuss depending on whether b ≥ 0 or b ≤ 0
    · Assume that b ≥ 0
      Assume for contradiction that ¬ ((a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0))
      Since ¬ ((a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0)) we get that (a < 0 ∨ b < 0) ∧ (a > 0 ∨ b > 0)
      We conclude by contradicting (a < 0 ∨ b < 0) ∧ (a > 0 ∨ b > 0) and a * b ≥ 0
    · Assume that b ≤ 0
      Let's prove that a ≤ 0 ∧ b ≤ 0
      · Since a ≤ 0 and b ≤ 0 we conclude that a ≤ 0 ∧ b ≤ 0
QED
```

Below is an example of how to do a proof by double containment (Strategy 2.1.15) in Waterproof.
This can be done by using `Let's first prove that ...` and `Let's now prove that ...` for the two inclusions.
This also shows how you can refer to an earlier result in Waterproof.
We can provide parameters `a` and `b` to the lemma by writing `applied to a and b`, and the fact that `a * b ≥ 0`
by writing `using that a * b ≥ 0`.

```lean
Example "2.1.16"
  Given:
  Assume:
  Conclusion: {x | x ^ 2 ≤ 1} = [-1, 1]
Proof:
  Let's first prove that {x | x ^ 2 ≤ 1} ⊆ [-1, 1]
  · Fix x
    Assume that x ^ 2 ≤ 1
    Since x ^ 2 ≤ 1 we get that (1 - x) * (1 + x) ≥ 0
    Fact : (1 - x ≥ 0 ∧ 1 + x ≥ 0) ∨ (1 - x ≤ 0 ∧ 1 + x ≤ 0) from multiplication_dichotomy
      applied to 1 - x and 1 + x using that (1 - x) * (1 + x) ≥ 0
    We discuss depending on whether (1 - x ≥ 0 ∧ 1 + x ≥ 0) or (1 - x ≤ 0 ∧ 1 + x ≤ 0)
    · Assume that 1 - x ≥ 0 ∧ 1 + x ≥ 0
      Since 1 - x ≥ 0 and 1 + x ≥ 0 we conclude that x ∈ [-1, 1]
    · Assume that 1 - x ≤ 0 ∧ 1 + x ≤ 0
      Let's prove it's contradictory
      We conclude by contradicting 1 - x ≤ 0 ∧ 1 + x ≤ 0
  Let's now prove that [-1, 1] ⊆ {x | x ^ 2 ≤ 1}
  · Fix x ∈ [-1, 1]
    Since x ∈ [-1, 1] we get that -1 ≤ x and x ≤ 1
    Since -1 ≤ x and x ≤ 1 we get that |x| ≤ 1
    Since |x| ≤ 1 we conclude that x ^ 2 ≤ 1
QED
```

Below are two exercises to practice proof by double containment (Strategy 2.1.15). 

::::multilean
```lean
Exercise "2.1.17"
  Given:
  Assume:
  Conclusion: {x | x * x < x} = (0, 1)
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
Exercise "2.1.18a"
  Given:
  Assume:
  Conclusion: {0, 1} = {1, 0}
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
