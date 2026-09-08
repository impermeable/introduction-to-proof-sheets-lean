/-
  Integer lemmas for Waterproof exercise sheets.

  Even/odd parity notation, witness extraction, addition/multiplication
  parity rules, and miscellaneous integer identities.
-/

import Verbose.English.All
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

open Finset

-- ══════════════════════════════════════════════════════════════
-- § Notation
-- ══════════════════════════════════════════════════════════════

notation:50 n " is even" => Even n
notation:50 n " is odd" => Odd n

-- [a, b] notation for Finset.Icc a b (scoped).
-- `open scoped Bewijzen.FinsetIntervalNotation` in any sheet that writes
-- ∑ k ∈ [a, b], f k  (reads like ∑_{k=a}^{b} f(k) on paper).
-- Priority 1100 beats list notation (1000) for two-element [a,b].
-- Single-element lists like [x] still work (different syntax branch).
-- Cannot coexist with Bewijzen.IntervalNotation (ℝ intervals) in the same scope.
-- The body must stay the bare constant `Finset.Icc a b` (NO type ascription):
-- the pretty-printer maps the constant back to `[a, b]` only for a plain
-- constant application; an ascribed body makes goals print `Finset.Icc a b`.
namespace Bewijzen.FinsetIntervalNotation
scoped notation (priority := 1100) "[" a ", " b "]" => Finset.Icc a b
end Bewijzen.FinsetIntervalNotation

-- Equivalence: Finset.Icc 0 n = Finset.range (n + 1).
-- Used to convert between the two representations of "sum from 0 to n".
@[simp] lemma icc_zero_eq_range (n : ℕ) : Finset.Icc 0 n = Finset.range (n + 1) :=
  Eq.symm $ Nat.range_succ_eq_Icc_zero n

-- ══════════════════════════════════════════════════════════════
-- § Witness extraction / construction
-- ══════════════════════════════════════════════════════════════

lemma even_witnesses {n : ℤ} (h : Even n) : ∃ k : ℤ, n = 2 * k :=
  let ⟨k, hk⟩ := h; ⟨k, by linarith⟩

lemma odd_witnesses {n : ℤ} (h : Odd n) : ∃ k : ℤ, n = 2 * k + 1 :=
  let ⟨k, hk⟩ := h; ⟨k, by linarith⟩

lemma even_of_two_mul {n k : ℤ} (_ : n = 2 * k) : Even n := ⟨k, by linarith⟩

lemma odd_of_two_mul_add_one {n m : ℤ} (_ : n = 2 * m + 1) : Odd n := ⟨m, by linarith⟩

-- ══════════════════════════════════════════════════════════════
-- § Addition parity rules
-- ══════════════════════════════════════════════════════════════

lemma even_add_even {a b : ℤ} (_ : Even a) (_ : Even b) : Even (a + b) := by
  obtain ⟨k, hk⟩ := ‹Even a›; obtain ⟨l, hl⟩ := ‹Even b›
  exact ⟨k + l, by omega⟩

lemma odd_add_odd {a b : ℤ} (_ : Odd a) (_ : Odd b) : Even (a + b) := by
  obtain ⟨k, hk⟩ := ‹Odd a›; obtain ⟨l, hl⟩ := ‹Odd b›
  exact ⟨k + l + 1, by omega⟩

lemma even_add_odd {a b : ℤ} (_ : Even a) (_ : Odd b) : Odd (a + b) := by
  obtain ⟨k, hk⟩ := ‹Even a›; obtain ⟨l, hl⟩ := ‹Odd b›
  exact ⟨k + l, by omega⟩

lemma odd_add_even {a b : ℤ} (_ : Odd a) (_ : Even b) : Odd (a + b) := by
  obtain ⟨k, hk⟩ := ‹Odd a›; obtain ⟨l, hl⟩ := ‹Even b›
  exact ⟨k + l, by omega⟩

-- ══════════════════════════════════════════════════════════════
-- § Multiplication parity rules
-- ══════════════════════════════════════════════════════════════

lemma odd_mul_odd {a b : ℤ} (_ : Odd a) (_ : Odd b) : Odd (a * b) :=
  Odd.mul ‹Odd a› ‹Odd b›

lemma even_mul {a b : ℤ} (_ : Even a) : Even (a * b) :=
  Even.mul_right ‹Even a› b

lemma mul_even {a b : ℤ} (_ : Even b) : Even (a * b) :=
  Even.mul_left ‹Even b› a

-- ══════════════════════════════════════════════════════════════
-- § Excluded middle rules
-- ══════════════════════════════════════════════════════════════

lemma even_and_odd_false {n : ℤ} (_ : Odd n) (_ : Even n) : False := by
  obtain ⟨k, hk⟩ := ‹Even n›; obtain ⟨l, hl⟩ := ‹Odd n›; omega

lemma even_not_odd {n : ℤ} (h : Even n) : ¬ Odd n :=
  Int.not_odd_iff_even.mpr h
  
lemma odd_not_even {n : ℤ} (h : Odd n) : ¬ Even n := 
  Int.not_even_iff_odd.mpr h

lemma not_even_odd {n : ℤ} (h : ¬ Even n) : Odd n :=
  Int.not_even_iff_odd.mp h

lemma not_odd_even {n : ℤ} (h : ¬ Odd n) : Even n :=
  Int.not_odd_iff_even.mp h

-- ══════════════════════════════════════════════════════════════
-- § Miscellaneous integer identities
-- ══════════════════════════════════════════════════════════════

-- Cube-successor expansion: (n+1)³ - 1 = 3*(m + n² + n) when n³ = 3*m.
lemma expand_cube_succ (n m : ℤ) (hm : n ^ 3 = 3 * m) :
    (n + 1) ^ 3 - 1 = 3 * (m + n ^ 2 + n) := by ring_nf; linarith

-- ══════════════════════════════════════════════════════════════
-- § Sum bridge lemmas for weak induction
-- ══════════════════════════════════════════════════════════════

-- Sum-range expansion: replaces ∑ k ∈ range (n+1), k with ∑ j ∈ range n, j + n.
-- This is used in the induction step of ∑_{k=0}^n k = n(n+1)/2.
lemma sum_range_succ {s : ℕ} : ∑ k ∈ Finset.range (s + 1), k = (∑ j ∈ Finset.range s, j) + s := by
  rw [Finset.sum_range_succ]

-- Bridge lemma: given IH, prove the induction step for ∑_{k=0}^{n+1} k = (n+1)(n+2)/2.
lemma sum_range_succ_and_subst_final {n : ℕ} (h : ∑ j ∈ Finset.range (n + 1), j = n * (n + 1) / 2) :
  ∑ k ∈ Finset.range ((n + 1) + 1), k = (n + 1) * ((n + 1) + 1) / 2 := by
  rw [Finset.sum_range_succ, h]
  ring_nf
  omega

-- Split off the last term of a sum over an Icc interval:
-- ∑_{k=a}^{n+1} f k = (∑_{k=a}^{n} f k) + f (n+1).
-- This is "by definition of sum" on paper, and is the key step
-- in every induction proof about sums.
lemma sum_icc_succ_top (a n : ℕ) (f : ℕ → ℕ) (h_le : a ≤ n) :
    (∑ k ∈ Finset.Icc a (n + 1), f k) = (∑ k ∈ Finset.Icc a n, f k) + f (n + 1) := by
  have h_not_mem : (n + 1 : ℕ) ∉ Finset.Icc a n := by
    simp [Finset.mem_Icc]
  rw [← insert_Icc_right_eq_Icc_add_one (le_trans h_le (Nat.le_succ _)), Finset.sum_insert h_not_mem]
  rw [add_comm]

addAnonymousComputeLemma sum_icc_succ_top

-- Special case for sums starting at 0: no proof argument needed.
-- Registered for `by computation` in induction proofs.
lemma sum_icc_zero_succ_top (n : ℕ) (f : ℕ → ℕ) :
    (∑ k ∈ Finset.Icc 0 (n + 1), f k) = (∑ k ∈ Finset.Icc 0 n, f k) + f (n + 1) := by
  have h_not_mem : n + 1 ∉ Finset.Icc 0 n := by simp
  rw [← insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert h_not_mem]
  rw [add_comm]

addAnonymousComputeLemma sum_icc_zero_succ_top

-- Concrete compute lemmas for common sum bodies (unification-friendly).
lemma sum_icc_zero_succ_id (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 (n + 1), k = (∑ k ∈ Finset.Icc 0 n, k) + (n + 1) :=
  by exact sum_icc_zero_succ_top n (fun k => k)

lemma sum_icc_zero_succ_sq (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 (n + 1), k ^ 2 = (∑ k ∈ Finset.Icc 0 n, k ^ 2) + (n + 1) ^ 2 :=
  by exact sum_icc_zero_succ_top n (fun k => k ^ 2)

lemma sum_icc_zero_succ_cubed (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 (n + 1), k ^ 3 = (∑ k ∈ Finset.Icc 0 n, k ^ 3) + (n + 1) ^ 3 :=
  by exact sum_icc_zero_succ_top n (fun k => k ^ 3)

lemma sum_icc_zero_succ_pow_two (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 (n + 1), 2 ^ k = (∑ k ∈ Finset.Icc 0 n, 2 ^ k) + 2 ^ (n + 1) :=
  by exact sum_icc_zero_succ_top n (fun k => 2 ^ k)

addAnonymousComputeLemma sum_icc_zero_succ_id
addAnonymousComputeLemma sum_icc_zero_succ_sq
addAnonymousComputeLemma sum_icc_zero_succ_cubed
addAnonymousComputeLemma sum_icc_zero_succ_pow_two

-- Polymorphic version for real-valued sums (geometric series, etc.).
-- The type variable α must be an AddCommMonoid (e.g., ℝ, ℤ, ℕ).
lemma sum_icc_zero_succ_poly {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (∑ k ∈ Finset.Icc 0 (n + 1), f k) = (∑ k ∈ Finset.Icc 0 n, f k) + f (n + 1) := by
  have h_not_mem : n + 1 ∉ Finset.Icc 0 n := by simp
  rw [← insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert h_not_mem]
  rw [add_comm]

addAnonymousComputeLemma sum_icc_zero_succ_poly

-- ══════════════════════════════════════════════════════════════
-- § Divisibility by primes: p ∣ a² → p ∣ a for prime p
-- ══════════════════════════════════════════════════════════════

-- Lemma: if a prime p divides a², then p divides a.
-- Proof: by Euclid's lemma (p ∣ a*b → p ∣ a ∨ p ∣ b) applied to a*a.
lemma prime_dvd_sq {p a : ℕ} (hp : Nat.Prime p) (h : p ∣ a ^ 2) : p ∣ a := by
  have h_mul : p ∣ a * a := by simpa [pow_two] using h
  have : p ∣ a ∨ p ∣ a := hp.dvd_mul.mp h_mul
  cases this with
  | inl ha => exact ha
  | inr ha => exact ha

-- Lemma: if 3 divides n², then 3 divides n.
-- Proof: write n = 3*k + r with r ∈ {0, 1, 2}.
-- If r = 0 then 3 | n. If r = 1 or r = 2 then n² ≡ 1 (mod 3), contradiction.
lemma three_dvd_sq {n : ℕ} (h : 3 ∣ n ^ 2) : 3 ∣ n := by
  -- Write n = 3*k + r with r < 3
  obtain ⟨k, r, hr_lt, hn⟩ : ∃ k r, r < 3 ∧ n = 3 * k + r := by
    use n / 3, n % 3
    constructor
    · exact Nat.mod_lt n (by decide)
    · omega
  -- r ∈ {0, 1, 2}
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr with (hr | hr | hr)
  · -- Case r = 0: n = 3*k, so 3 | n
    rw [hr] at hn
    use k
    linarith
  · -- Case r = 1: n = 3*k + 1, n² = 9k² + 6k + 1 = 3*(3k² + 2k) + 1
    rw [hr] at hn
    have : n = 3 * k + 1 := by linarith
    rw [this] at h
    have h2 : (3 * k + 1) ^ 2 = 3 * (3 * k ^ 2 + 2 * k) + 1 := by ring_nf
    rw [h2] at h
    obtain ⟨m, hm⟩ := h
    omega
  · -- Case r = 2: n = 3*k + 2, n² = 9k² + 12k + 4 = 3*(3k² + 4k + 1) + 1
    rw [hr] at hn
    have : n = 3 * k + 2 := by linarith
    rw [this] at h
    have h2 : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring_nf
    rw [h2] at h
    obtain ⟨m, hm⟩ := h
    omega

-- ══════════════════════════════════════════════════════════════
-- § Nat.dvd_pow_two_add_one patterns
-- ══════════════════════════════════════════════════════════════
-- Bridge lemmas for divisibility patterns involving expressions like 2^n + 1.

-- Bridge lemma: general pattern for a + b ∣ a^n + b^n when n is odd.
-- If a + b divides a + b, then a + b divides a^(2k+1) + b^(2k+1) for all k ≥ 0.
-- Special case: 3 | 2^n + 1 when n is odd (since a=2, b=1, a+b=3).
-- Proof: by induction on k, using a^(n+2) + b^(n+2) = a^2(a^n + b^n) + (b^2 - a^2)b^n.
lemma dvd_pow_add_pow_of_odd {a b : ℤ} (n : ℕ) (h : Odd n) : (a + b) ∣ a ^ n + b ^ n := by
  cases h with
  | intro k hk =>
    subst n
    induction k with
    | zero =>
      -- n = 1: a + b ∣ a + b
      use 1
      ring
    | succ k ih =>
      -- IH: a + b ∣ a^(2k+1) + b^(2k+1)
      -- Goal: a + b ∣ a^(2(k+1)+1) + b^(2(k+1)+1) = a^(2k+3) + b^(2k+3)
      -- Key identity: a^(2k+3) + b^(2k+3)
      --   = a^2 · a^(2k+1) + b^2 · b^(2k+1)
      --   = a^2(a^(2k+1) + b^(2k+1)) + (b^2 - a^2)b^(2k+1)
      --   = a^2(a^(2k+1) + b^(2k+1)) + (b-a)(b+a)b^(2k+1)
      -- Both terms on the right are divisible by a+b
      obtain ⟨m, hm⟩ := ih
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
      have h : a ^ (2 * k + 3) + b ^ (2 * k + 3)
          = a ^ 2 * (a ^ (2 * k + 1) + b ^ (2 * k + 1)) + (b - a) * (a + b) * b ^ (2 * k + 1) := by
        ring
      rw [h]
      -- Both summands are divisible by (a+b):
      --   a^2 * (a^(2k+1) + b^(2k+1)) = a^2 * (a+b) * m = (a+b) * (a^2 * m)
      --   (b-a) * (a+b) * b^(2k+1) = (a+b) * (b-a) * b^(2k+1)
      apply dvd_add
      · use a ^ 2 * m
        rw [hm]
        ring
      · use (b - a) * b ^ (2 * k + 1)
        ring


