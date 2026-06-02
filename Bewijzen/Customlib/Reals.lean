/-
  Real number lemmas for Waterproof exercise sheets.

  Square notation and helpers for unique-existence proofs
  involving square roots, quadratics, and sum-of-squares.
-/

import Verbose.English.All
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- ══════════════════════════════════════════════════════════════
-- § Notation
-- ══════════════════════════════════════════════════════════════

notation:50 n " is square" => IsSquare n

-- ══════════════════════════════════════════════════════════════
-- § Square root helpers
-- ══════════════════════════════════════════════════════════════

lemma sqrt_pos_and_sq {a : ℝ} (_ : a > 0) : √a > 0 ∧ √a ^ 2 = a :=
  ⟨Real.sqrt_pos.mpr ‹_›, Real.sq_sqrt (le_of_lt ‹_›)⟩
addAnonymousGoalSplittingLemma sqrt_pos_and_sq

lemma eq_sqrt_of_pos_sq {x a : ℝ} (hx : x > 0) (_ : a > 0) (hxa : x ^ 2 = a) : x = √a := by rw [← hxa, Real.sqrt_sq hx.le]
addAnonymousGoalSplittingLemma eq_sqrt_of_pos_sq

-- ══════════════════════════════════════════════════════════════
-- § Quadratic / sum-of-squares helpers
-- ══════════════════════════════════════════════════════════════

lemma quad_root {x a : ℝ} (h : x ^ 2 + 2 * a * x + a ^ 2 = 0) : x = -a := by nlinarith [sq_nonneg (x + a)]
addAnonymousGoalSplittingLemma quad_root

lemma neg_a_is_root (a : ℝ) : (-a) ^ 2 + 2 * a * (-a) + a ^ 2 = 0 := by ring
addAnonymousGoalSplittingLemma neg_a_is_root

lemma sq_sum_zero_imp {b : ℝ} (h : ∃ x : ℝ, x ^ 2 + b ^ 2 = 0) : b = 0 := by
  obtain ⟨x, hx⟩ := h; nlinarith [sq_nonneg x, sq_nonneg b]
addAnonymousGoalSplittingLemma sq_sum_zero_imp
