import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Rational
import Bewijzen.Customlib.Lists
open WaterproofGenre

addAnonymousGoalSplittingLemma rationalArithmetic

-- Definition 5.1.36: transitive (Bewijzen.Customlib.Functions)

-- Example 5.1.38
Example "5.1.38"
  Given:
  Assume:
  Conclusion: (fun a b : ℝ => (b - a) is rational) is transitive
Proof:
  Fix a b c
  Assume that (b - a) is rational
  Assume that (c - b) is rational
  Since (c - b) is rational and (b - a) is rational we get that (c - b) + (b - a) is rational
  Since (c - b) + (b - a) is rational and (c - b) + (b - a) = c - a we conclude that (c - a) is rational
QED

-- Exercise 5.1.39


Exercise "5.1.39"
  Given: (Z : Type)
  Assume:
  Conclusion: (fun A B : Set Z => A ⊆ B) is transitive
Proof:
  Fix A B C
  Assume that A ⊆ B
  Assume that B ⊆ C
  Fix x ∈ A
  Since A ⊆ B and x ∈ A we get that x ∈ B
  Since B ⊆ C and x ∈ B we conclude that x ∈ C
QED
