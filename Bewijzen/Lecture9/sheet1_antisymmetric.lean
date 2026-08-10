import WaterproofGenre
import Verbose.English.All
import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Lists
open WaterproofGenre

addAnonymousGoalSplittingLemma subsetTheory
addAnonymousGoalSplittingLemma orderAntisymmetry

-- Definition 5.1.30: antisymmetric (Bewijzen.Customlib.Functions)

-- Example 5.1.32
Example "5.1.32"
  Given:
  Assume:
  Conclusion: (fun a b : ℝ => a ≤ b) is antisymmetric
Proof:
  Fix a b
  Assume that a ≤ b
  Assume that b ≤ a
  Since a ≤ b and b ≤ a we conclude that a = b
QED

-- Exercise 5.1.34

Exercise "5.1.34"
  Given: (Z : Type)
  Assume:
  Conclusion: (fun A B : Set Z => A ⊆ B) is antisymmetric
Proof:
  Fix A B
  Assume that A ⊆ B
  Assume that B ⊆ A
  Since A ⊆ B and B ⊆ A we conclude that A = B
QED
