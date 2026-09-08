/-
  Natural number lemmas for Waterproof exercise sheets.

  Covers: sum reindexing lemmas, factorial identities, and miscellaneous
  natural number arithmetic useful for induction proofs.

  Register lemmas in each sheet's doc block with addAnonymousGoalSplittingLemma;
  no registrations live here.
-/

import Verbose.English.All
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic

open Finset

-- ══════════════════════════════════════════════════════════════
-- § Sum reindexing lemmas
-- ══════════════════════════════════════════════════════════════

-- Split off the first term from a sum:
-- ∑_{i=0}^{n} f i = f 0 + ∑_{j=0}^{n-1} f (j+1).
-- This is useful in induction proofs where you need to separate
-- the 0th term from the induction hypothesis on the remaining sum.
lemma sum_range_split_first (α : Type*) [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ∑ i ∈ range (n + 1), f i = f 0 + ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ, add_assoc]

addAnonymousGoalSplittingLemma sum_range_split_first

-- Shifted sum: ∑_{i=0}^{n-1} f (i + m) = ∑_{j=0}^{n-1} f (j + m).
-- This is a renaming identity (both sides are identical).
lemma sum_range_shift (α : Type*) [AddCommMonoid α] (n : ℕ) (m : ℕ) (f : ℕ → α) :
    ∑ i ∈ range n, f (i + m) = ∑ j ∈ range n, f (j + m) := rfl

-- ══════════════════════════════════════════════════════════════
-- § Factorial identities
-- ══════════════════════════════════════════════════════════════

-- (n + 1)! = (n + 1) * n!
lemma factorial_succ (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  rw [Nat.factorial_succ]

addAnonymousGoalSplittingLemma factorial_succ

-- 0! = 1
lemma factorial_zero : Nat.factorial 0 = 1 := by decide

addAnonymousGoalSplittingLemma factorial_zero

-- 1! = 1
lemma factorial_one : Nat.factorial 1 = 1 := by decide

addAnonymousGoalSplittingLemma factorial_one

-- n! = n * (n-1)! for n ≥ 1
lemma factorial_succ_eq {n : ℕ} (h : n ≥ 1) : Nat.factorial n = n * Nat.factorial (n - 1) := by
  cases n with
  | zero => contradiction
  | succ n => simp [Nat.factorial]

addAnonymousGoalSplittingLemma factorial_succ_eq
