/-
  Real number lemmas for Waterproof exercise sheets.

  Covers: square/sqrt helpers, quadratic identities, interval notation and
  membership, interval subset characterisations, real dichotomies, sign
  arithmetic, and pair-set bridge lemmas.

  Notation is opt-in via scoped namespaces:
    open scoped Bewijzen.IntervalNotation   -- [a,b], (a,b), [a,b), (a,b], [a]
    open scoped Bewijzen.PairSetNotation    -- {a, b} as a two-element ℝ-set

  Register lemmas in each sheet's doc block with addAnonymousGoalSplittingLemma;
  no registrations live here.
-/

import Verbose.English.All
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Interval.Set.Basic

-- ══════════════════════════════════════════════════════════════
-- § Notation abbreviations
-- ══════════════════════════════════════════════════════════════

notation:50 n " is square" => IsSquare n

-- Backing interval abbreviations; sheets use Bewijzen.IntervalNotation for syntax.
abbrev Icc_R (a b : ℝ) := Set.Icc a b
abbrev Ioo_R (a b : ℝ) := Set.Ioo a b
abbrev Ico_R (a b : ℝ) := Set.Ico a b
abbrev Ioc_R (a b : ℝ) := Set.Ioc a b
abbrev Iio_R (a : ℝ)   := Set.Iio a
abbrev Iio_N (a : ℕ)   := Set.Iio a

-- Scoped interval notation.  `open scoped Bewijzen.IntervalNotation` in any sheet
-- that writes [a,b], (a,b), [a,b), (a,b], or [a] for intervals.
-- Priority 1100 beats list notation (1000) for [a,b] and the builtin paren for (a,b).
namespace Bewijzen.IntervalNotation
scoped notation (priority := 1100) "[" a ", " b "]"  => Icc_R a b
scoped notation (priority := 1100) "(" a ", " b ")"  => Ioo_R a b
scoped notation                    "[" a ", " b ")"  => Ico_R a b
scoped notation                    "(" a ", " b "]"  => Ioc_R a b
scoped notation (priority := 1100) "[" a "]"          => Iio_N a
end Bewijzen.IntervalNotation

-- ══════════════════════════════════════════════════════════════
-- § Square root helpers
-- ══════════════════════════════════════════════════════════════

lemma sqrt_pos_and_sq {a : ℝ} (_ : a > 0) : √a > 0 ∧ √a ^ 2 = a :=
  ⟨Real.sqrt_pos.mpr ‹_›, Real.sq_sqrt (le_of_lt ‹_›)⟩

lemma eq_sqrt_of_pos_sq {x a : ℝ} (hx : x > 0) (_ : a > 0) (hxa : x ^ 2 = a) : x = √a := by
  rw [← hxa, Real.sqrt_sq hx.le]

-- ══════════════════════════════════════════════════════════════
-- § Quadratic / sum-of-squares helpers
-- ══════════════════════════════════════════════════════════════

lemma quad_root {x a : ℝ} (h : x ^ 2 + 2 * a * x + a ^ 2 = 0) : x = -a := by
  nlinarith [sq_nonneg (x + a)]

lemma neg_a_is_root (a : ℝ) : (-a) ^ 2 + 2 * a * (-a) + a ^ 2 = 0 := by ring

lemma sq_sum_zero_imp {b : ℝ} (h : ∃ x : ℝ, x ^ 2 + b ^ 2 = 0) : b = 0 := by
  obtain ⟨x, hx⟩ := h; nlinarith [sq_nonneg x, sq_nonneg b]

-- ══════════════════════════════════════════════════════════════
-- § Square / absolute value lemmas
-- ══════════════════════════════════════════════════════════════

lemma sq_le_one_of_abs (x : ℝ) (h : |x| ≤ 1) : x ^ 2 ≤ 1 := by
  have h_pos : 0 ≤ |x| := abs_nonneg x
  have : |x|^2 ≤ 1^2 := by nlinarith [h_pos, h]
  rwa [sq_abs, one_pow] at this

lemma sq_le_one_imp_mul_nonneg (x : ℝ) (h : x ^ 2 ≤ 1) : (1 - x)*(1 + x) ≥ 0 := by nlinarith

-- ══════════════════════════════════════════════════════════════
-- § Interval membership helpers
-- ══════════════════════════════════════════════════════════════

-- (0, 1) intro and elim, used in set-characterisation exercises.
lemma gt_zero_and_lt_one_to_Ioo (x : ℝ) (h1 : x > 0) (h2 : x < 1) : x ∈ Set.Ioo 0 1 := ⟨h1, h2⟩
lemma mem_Ioo_extract (x : ℝ) (h : x ∈ Set.Ioo 0 1) : 0 < x ∧ x < 1 := ⟨h.1, h.2⟩

-- Left endpoint belongs to [a, b] when a ≤ b.
lemma mem_Icc_left {a b : ℝ} (h : a ≤ b) : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr h

-- Left endpoint belongs to [a, b) when a < b.
lemma mem_Ico_self {a b : ℝ} (hab : a < b) : a ∈ Set.Ico a b := ⟨le_refl a, hab⟩

-- Right endpoint belongs to (a, b] when a < b (symmetric to mem_Ico_self).
lemma mem_Ioc_self {a b : ℝ} (hab : a < b) : b ∈ Set.Ioc a b := ⟨hab, le_refl b⟩

-- a < b and b ≤ c: weak conclusion a ≤ c (symmetric to lt_of_lt_of_le which gives a < c).
lemma lt_le_imp_le {a b c : ℝ} (h1 : a < b) (h2 : b ≤ c) : a ≤ c :=
  (lt_of_lt_of_le h1 h2).le

-- Midpoint of (a, b) lies in (a, b) when a < b.
lemma midpoint_mem_Ioo {a b : ℝ} (h : a < b) : (a + b) / 2 ∈ Set.Ioo a b := by
  constructor <;> linarith

-- Bridge for [-1, 1] membership from the form students derive after factoring x²≤1:
--   (1-x)*(1+x) ≥ 0  →  1-x ≥ 0 ∧ 1+x ≥ 0  →  x ∈ [-1, 1].
-- Kept specific to this interval: the hypothesis form `1+x ≥ 0` differs syntactically
-- from the generalised `x - a ≥ 0` (with a = -1), which would break Verbose matching.
lemma Icc_R_intro {x : ℝ} (h1 : 1 - x ≥ 0) (h2 : 1 + x ≥ 0) : x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

-- ══════════════════════════════════════════════════════════════
-- § Interval subset helpers
-- ══════════════════════════════════════════════════════════════

-- [a, b) ⊆ (c, d] implies a > c and b ≤ d.
lemma Ico_sub_Ioc_forward {a b c d : ℝ} (hab : a < b) (_hcd : c < d)
    (h : Set.Ico a b ⊆ Set.Ioc c d) : a > c ∧ b ≤ d := by
  have ha : a ∈ Set.Ico a b := ⟨le_refl a, hab⟩
  have had := h ha
  constructor
  · exact had.1
  · by_contra hbd
    push Not at hbd
    have hda : a ≤ d := had.2
    have hm : (d + b) / 2 ∈ Set.Ico a b := by constructor <;> linarith
    have := h hm
    linarith [this.2]

-- [a, b) ⊆ (c, d] implies b ≤ d (weaker; implicit hab for cleaner Verbose output).
lemma Ico_sub_Ioc_forward_b_le_d' {a b c d : ℝ} {hab : a < b}
    (h : Set.Ico a b ⊆ Set.Ioc c d) : b ≤ d := by
  have ha : a ∈ Set.Ico a b := ⟨le_refl a, hab⟩
  have ha' : a ∈ Set.Ioc c d := h ha
  have ha_le_d : a ≤ d := ha'.2
  by_contra hbd
  push Not at hbd
  have hm : (d + b) / 2 ∈ Set.Ico a b := by constructor <;> linarith
  have hcd := h hm
  linarith [hcd.2]

-- ══════════════════════════════════════════════════════════════
-- § Real dichotomies
-- ══════════════════════════════════════════════════════════════

lemma ge_or_le_zero {x : ℝ} : x ≥ 0 ∨ x ≤ 0 := by
  by_cases hx : x ≥ 0
  · exact Or.inl hx
  · exact Or.inr (by linarith)

lemma le_or_gt_zero {x : ℝ} : x ≤ 0 ∨ x > 0 := by
  by_cases hx : x ≤ 0
  · exact Or.inl hx
  · exact Or.inr (by linarith)

lemma gt_zero_or_le_zero {x : ℝ} : x > 0 ∨ x ≤ 0 := by
  by_cases hx : x > 0
  · exact Or.inl hx
  · exact Or.inr (by linarith)

lemma lt_or_ge_one {x : ℝ} : x < 1 ∨ x ≥ 1 := by
  by_cases hx : x < 1
  · exact Or.inl hx
  · exact Or.inr (by linarith)

lemma ge_and_lt_real_false {a b : ℝ} (h1 : a ≥ b) (h2 : a < b) : False := by linarith

-- ══════════════════════════════════════════════════════════════
-- § Sign arithmetic
-- ══════════════════════════════════════════════════════════════

lemma root_gt_zero {x : ℝ} (h1 : 0 < x) (h2 : x < 1) : x * x < x := by nlinarith

lemma mul_self_ge_self_of_ge_one {x : ℝ} (h : x ≥ 1) : x * x ≥ x := by nlinarith
lemma mul_self_ge_self_of_le_zero {x : ℝ} (h : x ≤ 0) : x * x ≥ x := by nlinarith

-- 1 - x ≤ 0 and 1 + x ≤ 0 cannot both hold simultaneously.
lemma bound_contra {x : ℝ} (h : 1 - x ≤ 0 ∧ 1 + x ≤ 0) : False := by linarith

-- De Morgan bridge: ¬((a≥0 ∧ b≥0) ∨ (a≤0 ∧ b≤0)) decomposes into sign disjunctions.
lemma de_morgan_bridge {a b : ℝ}
    (h : ¬((a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0)))
    : (a < 0 ∨ b < 0) ∧ (a > 0 ∨ b > 0) := by
  have h_not_or := not_or.mp h
  have h_left_or := not_and_or.mp h_not_or.1
  have h_right_or := not_and_or.mp h_not_or.2
  have h_a_neg : a < 0 ∨ b < 0 := by
    rcases h_left_or with h_a | h_b
    · exact Or.inl (not_le.mp h_a)
    · exact Or.inr (not_le.mp h_b)
  have h_b_pos : a > 0 ∨ b > 0 := by
    rcases h_right_or with h_a | h_b
    · exact Or.inl (not_le.mp h_a)
    · exact Or.inr (not_le.mp h_b)
  exact ⟨h_a_neg, h_b_pos⟩

-- Signed disjunctions together with a * b ≥ 0 yield a contradiction.
lemma contradiction_from_dm {a b : ℝ}
    (h : (a < 0 ∨ b < 0) ∧ (a > 0 ∨ b > 0)) (hab : a * b ≥ 0) : False := by
  rcases h.1 with ha | hb
  · rcases h.2 with ha' | hb'
    · linarith
    · nlinarith
  · rcases h.2 with ha' | hb'
    · nlinarith
    · linarith

-- a * b ≥ 0 implies the factors share sign (or one is zero).
lemma multiplication_dichotomy_bridge (a b : ℝ) (h : a * b ≥ 0) :
    (a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0) := by
  by_contra h_not
  exact contradiction_from_dm (de_morgan_bridge h_not) h

-- ══════════════════════════════════════════════════════════════
-- § Pair sets on ℝ
-- ══════════════════════════════════════════════════════════════

-- Two-element ℝ-subset; backing definition for Bewijzen.PairSetNotation.
def rpair (a b : ℝ) : Set ℝ := {a, b}

-- Scoped pair-set notation.  `open scoped Bewijzen.PairSetNotation` in sheets that
-- write {a, b} for a two-element real set (priority 1100 overrides default syntax).
namespace Bewijzen.PairSetNotation
scoped notation (priority := 1100) "{" a ", " b "}" => rpair a b
end Bewijzen.PairSetNotation

lemma mem_pair_cases (x a b : ℝ) (h : x ∈ rpair a b) : x = a ∨ x = b := h
lemma mem_pair_intro_left  (x a b : ℝ) (h : x = a) : x ∈ rpair a b := Or.inl h
lemma mem_pair_intro_right (x a b : ℝ) (h : x = b) : x ∈ rpair a b := Or.inr h
