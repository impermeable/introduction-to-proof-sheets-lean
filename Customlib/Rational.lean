/-
  Rational number lemmas for Waterproof exercise sheets.

  Defines IsRational/IsIrrational, notation, a heterogeneous
  ℤ/ℤ→ℝ division instance, and bridge lemmas for rational-number
  proofs (witness extraction, construction, arithmetic closure,
  negation, reciprocal).
-/

import Verbose.English.All

-- ══════════════════════════════════════════════════════════════
-- § Definitions & notation
-- ══════════════════════════════════════════════════════════════

abbrev IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x
notation:50 x " is rational" => IsRational x

abbrev IsIrrational (x : ℝ) : Prop := ¬IsRational x
notation:50 x " is irrational" => IsIrrational x

-- ══════════════════════════════════════════════════════════════
-- § Type coercions
-- ══════════════════════════════════════════════════════════════

-- Heterogeneous division ℤ / ℤ → ℝ
-- Allows writing "n / d : ℝ" when n d : ℤ without explicit coercions ↑n / ↑d.
-- Priority 50 (below default 100) so ordinary ℤ-division still wins in integer contexts;
-- this instance only fires when ℝ is forced by the surrounding expression.
noncomputable instance (priority := 50) intDivToReal : HDiv ℤ ℤ ℝ where
  hDiv n d := (n : ℝ) / d

-- ══════════════════════════════════════════════════════════════
-- § Witness extraction / construction
-- ══════════════════════════════════════════════════════════════

-- Witness extraction: if x is rational, extract integer numerator/denominator.
lemma rational_witnesses_int {x : ℝ} (h : IsRational x) :
  ∃ (n d : ℤ), d ≠ 0 ∧ x = (n : ℝ) / d := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.num, q.den, ?_, ?_⟩
  · exact_mod_cast q.den_pos.ne'
  · have : (q : ℝ) = (q.num : ℝ) / q.den := by
      simp [Rat.cast_def]
    simpa [this, eq_comm] using hq

-- Construction: build a rational from integer numerator/denominator.
lemma rational_from_ints {y : ℝ} {n d : ℤ} (_ : d ≠ 0) (h2 : y = ((n : ℝ) / d)) : IsRational y := by
  use ((n : ℚ) / (d : ℚ))
  push_cast
  exact h2.symm

-- Combine two integer fractions into one: m/e - n/d = (m*d - n*e) / (e*d).
lemma int_fractions_combine {y : ℝ} {m e n d : ℤ}
  (h1 : y = (m:ℝ) / e - (n:ℝ) / d) (he : e ≠ 0) (hd : d ≠ 0) : y = ((m:ℝ)*(d:ℝ) - (n:ℝ)*(e:ℝ)) / ((e:ℝ)*(d:ℝ)) := by
  have h_e : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have h_d : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  exact calc y = (m:ℝ) / e - (n:ℝ) / d := h1
             _ = ((m:ℝ)*(d:ℝ) - (n:ℝ)*(e:ℝ)) / ((e:ℝ)*(d:ℝ)) := by
               rw [div_sub_div _ _ h_e h_d]
               ring

-- Rationality from an expanded integer-fraction form.
lemma rational_from_unannotated_comb {y : ℝ} {m d n e : ℤ}
  (_ : e * d ≠ 0)
  (hy : y = ((m:ℝ)*(d:ℝ) - (n:ℝ)*(e:ℝ)) / ((e:ℝ)*(d:ℝ))) : IsRational y := by
  use (((m*d - n*e : ℤ) : ℚ) / ((e*d : ℤ) : ℚ))
  push_cast
  exact hy.symm

-- ══════════════════════════════════════════════════════════════
-- § Arithmetic closure
-- ══════════════════════════════════════════════════════════════

lemma rational_add {a b : ℝ} (_ : IsRational a) (_ : IsRational b) : IsRational (a + b) := by
  obtain ⟨qa, hqa⟩ := ‹IsRational a›
  obtain ⟨qb, hqb⟩ := ‹IsRational b›
  exact ⟨qa + qb, by push_cast; linarith⟩

lemma rational_sub {a b : ℝ} (_ : IsRational a) (_ : IsRational b) : IsRational (a - b) := by
  obtain ⟨qa, hqa⟩ := ‹IsRational a›
  obtain ⟨qb, hqb⟩ := ‹IsRational b›
  exact ⟨qa - qb, by push_cast; linarith⟩

lemma rational_mul {a b : ℝ} (_ : IsRational a) (_ : IsRational b) : IsRational (a * b) := by
  obtain ⟨qa, hqa⟩ := ‹IsRational a›
  obtain ⟨qb, hqb⟩ := ‹IsRational b›
  exact ⟨qa * qb, by push_cast; subst hqa; subst hqb; ring⟩

lemma rational_neg {a : ℝ} (_ : IsRational a) : IsRational (-a) := by
  obtain ⟨q, hq⟩ := ‹IsRational a›
  exact ⟨-q, by push_cast; linarith⟩

-- ══════════════════════════════════════════════════════════════
-- § Transfer & special forms
-- ══════════════════════════════════════════════════════════════

-- Transfer: if a = b and a is rational, then b is rational.
lemma rational_of_eq {a b : ℝ} (_ : IsRational a) (_ : a = b) : IsRational b := by
  obtain ⟨q, hq⟩ := ‹IsRational a›; exact ⟨q, by linarith⟩

-- Halving: 2 * x is rational implies x is rational.
lemma rational_of_two_mul {x : ℝ} (_ : IsRational (2 * x)) : IsRational x := by
  obtain ⟨q, hq⟩ := ‹IsRational (2 * x)›
  exact ⟨q / 2, by push_cast; linarith⟩

-- ══════════════════════════════════════════════════════════════
-- § Negation helpers
-- ══════════════════════════════════════════════════════════════

-- Negation: if -x = n/d then x = -n/d.
lemma eq_neg_frac_of_neg_eq_frac {x : ℝ} {n d : ℤ} (h : -x = n / d) : x = (-n : ℤ) / d := by
  have key : (-n : ℤ) / d = -(n / d : ℝ) := by push_cast [neg_div]; ring
  linarith

-- Negation: if d ≠ 0 and -x = n/d then x is rational.
lemma rational_of_neg_int_frac {x : ℝ} {n d : ℤ} (_ : d ≠ 0) (h : -x = n / d) : IsRational x := by
  use ((-n : ℤ) : ℚ) / (d : ℚ)
  push_cast [neg_div]
  linarith

-- Negation: if d ≠ 0 and x = -↑n/↑d then x is rational.
lemma rational_from_neg_cast_frac {y : ℝ} {n d : ℤ} (_hd : d ≠ 0) (h : y = -(↑n : ℝ) / ↑d) : IsRational y := by
  use ((-n : ℤ) : ℚ) / (d : ℚ)
  push_cast [neg_div] at *
  linarith

-- ══════════════════════════════════════════════════════════════
-- § Reciprocal helpers
-- ══════════════════════════════════════════════════════════════

-- Reciprocal: if x ≠ 0 and 1/x = n/d then n ≠ 0.
lemma ne_zero_of_recip_frac {n d : ℤ} {x : ℝ} (hx : x ≠ 0) (h : 1 / x = n / d) : n ≠ 0 := by
  intro hn
  subst hn
  simp at h
  exact hx h

-- Reciprocal: if x ≠ 0 and n ≠ 0 and 1/x = n/d then x = d/n.
-- hx and hn are implicit so Verbose's "Since 1/x = n/d we get that x = d/n" works.
lemma eq_of_recip_frac {n d : ℤ} {x : ℝ} {hx : x ≠ 0} {hn : n ≠ 0} (h : 1 / x = n / d) : x = d / n := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hd' : (d : ℝ) ≠ 0 := by
    intro hd_zero
    simp [hd_zero] at h
    exact hx h
  field_simp [hx, hn', hd'] at h ⊢
  linarith
