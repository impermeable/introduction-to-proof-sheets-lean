/-
  Integer lemmas for Waterproof exercise sheets.

  Even/odd parity notation, witness extraction, arithmetic closure,
  and miscellaneous integer identities.
-/

import Verbose.English.All

-- ══════════════════════════════════════════════════════════════
-- § Notation
-- ══════════════════════════════════════════════════════════════

notation:50 n " is even" => Even n
notation:50 n " is odd" => Odd n

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
-- § Contradiction
-- ══════════════════════════════════════════════════════════════

lemma even_and_odd_false {n : ℤ} (_ : Even n) (_ : Odd n) : False := by
  obtain ⟨k, hk⟩ := ‹Even n›; obtain ⟨l, hl⟩ := ‹Odd n›; omega

-- ══════════════════════════════════════════════════════════════
-- § Miscellaneous integer identities
-- ══════════════════════════════════════════════════════════════

-- Cube-successor expansion: (n+1)³ - 1 = 3*(m + n² + n) when n³ = 3*m.
lemma expand_cube_succ (n m : ℤ) (hm : n ^ 3 = 3 * m) :
    (n + 1) ^ 3 - 1 = 3 * (m + n ^ 2 + n) := by ring_nf; linarith
