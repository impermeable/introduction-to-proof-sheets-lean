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
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

-- ══════════════════════════════════════════════════════════════
-- § Elaboration of absolute values
-- ══════════════════════════════════════════════════════════════

-- Mathlib elaborates `|a|` as a bare `abs a`, so the expected type is never
-- pushed inside the bars: in `|(n + 1) / (n + 2) - 1|` with `n : ℕ` every
-- operation is read in ℕ (truncated subtraction, integer division) and only then
-- fails.  Re-elaborating through `unop%` — the same mechanism that already makes
-- `+`, `-`, `/` insert coercions — computes the type from the expected type and
-- coerces the leaves, so students can write the bars exactly as on paper.
macro_rules | `(|$a|) => `(unop% abs $a)

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
abbrev Ici_R (a : ℝ)   := Set.Ici a

-- Scoped interval notation.  `open scoped Bewijzen.IntervalNotation` in any sheet
-- that writes [a,b], (a,b), [a,b), (a,b], [a], or [a,∞) for intervals.
-- Priority 1100 beats list notation (1000) for [a,b] and the builtin paren for (a,b).
namespace Bewijzen.IntervalNotation
scoped notation (priority := 1100) "[" a ", " b "]"  => Icc_R a b
scoped notation (priority := 1100) "(" a ", " b ")"  => Ioo_R a b
scoped notation                    "[" a ", " b ")"  => Ico_R a b
scoped notation                    "(" a ", " b "]"  => Ioc_R a b
scoped notation (priority := 1100) "[" a "]"          => Iio_N a
scoped notation                    "[" a ", ∞)"       => Ici_R a
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

lemma nonneg_sq (a : ℝ) : a ^ 2 ≥ 0 := by
  exact sq_nonneg a

lemma pos_sq {a : ℝ} (_ : a ≠ 0) : a ^ 2 > 0 := by
  positivity

-- x ² = 0 forces x = 0 — used to step from `(y + a) ^ 2 = 0` to `y + a = 0`.
lemma zero_of_sq_eq_zero {x : ℝ} (h : x ^ 2 = 0) : x = 0 :=
  pow_eq_zero_iff (by norm_num) |>.mp h

-- a * b = 0 forces one factor to vanish — used to case-split a factored quadratic
-- such as `(y + √a) * (y - √a) = 0` into `y + √a = 0 ∨ y - √a = 0`.
lemma factors_zero {a b : ℝ} (h : a * b = 0) : a = 0 ∨ b = 0 := mul_eq_zero.mp h

lemma nonneg_add_pos (a b : ℝ) (_ : a ≥ 0) (_ : b > 0) : a + b > 0 := by
  positivity

lemma neg_a_is_root (a : ℝ) : (-a) ^ 2 + 2 * a * (-a) + a ^ 2 = 0 := by ring

-- A quantity cannot be both zero and strictly positive — closes the
-- `a ^ 2 + b ^ 2 = 0` vs `a ^ 2 + b ^ 2 > 0` contradiction.
lemma eq_and_gt_false {a b : ℝ} (h1 : a = b) (h2 : a > b) : False := by linarith

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

-- Generic [a, b] intro from its two defining inequalities.
lemma mem_Icc_bridge {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : x ∈ Set.Icc a b := ⟨h1, h2⟩

-- Bridge for [-1, 1] membership from the form students derive after factoring x²≤1:
--   (1-x)*(1+x) ≥ 0  →  1-x ≥ 0 ∧ 1+x ≥ 0  →  x ∈ [-1, 1].
-- Kept specific to this interval: the hypothesis form `1+x ≥ 0` differs syntactically
-- from the generalised `x - a ≥ 0` (with a = -1), which would break Verbose matching.
lemma Icc_R_intro {x : ℝ} (h1 : 1 - x ≥ 0) (h2 : 1 + x ≥ 0) : x ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

-- ══════════════════════════════════════════════════════════════
-- § Order antisymmetry
-- ══════════════════════════════════════════════════════════════

-- Antisymmetry of ≤ on ℝ — lets
-- "Since a ≤ b and b ≤ a we conclude that a = b" work directly.
lemma antisymm_le (a b : ℝ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  le_antisymm h1 h2

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
-- § Single intervals
-- ══════════════════════════════════════════════════════════════

-- X is expressible as a single interval (any combination of open/closed ends).
def IsSingleInterval (X : Set ℝ) : Prop :=
  ∃ a b : ℝ, X = Icc_R a b ∨ X = Ico_R a b ∨ X = Ioc_R a b ∨ X = Ioo_R a b

-- Scoped: `open scoped Bewijzen.IntervalNotation` reads `IsSingleInterval X`
-- as `X is an interval`. NB: the bare word `a` must not appear in the notation
-- string — it would be reserved as a token and break every later use of `a`
-- as a bound variable name (e.g. `Fix a`) in importing sheets.
namespace Bewijzen.IntervalNotation
scoped notation:50 X " is an interval" => IsSingleInterval X
end Bewijzen.IntervalNotation

lemma isSingleInterval_of_eq_Icc {X : Set ℝ} {a b : ℝ} (h : X = Icc_R a b) :
    IsSingleInterval X := ⟨a, b, Or.inl h⟩

lemma isSingleInterval_of_eq_Ico {X : Set ℝ} {a b : ℝ} (h : X = Ico_R a b) :
    IsSingleInterval X := ⟨a, b, Or.inr (Or.inl h)⟩

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

-- De Morgan bridge: ¬((a ≥ 0 ∧ b ≥ 0) ∨ (a ≤ 0 ∧ b ≤ 0)) decomposes into sign disjunctions.
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
-- § Linear equations
-- ══════════════════════════════════════════════════════════════

-- Cancel the nonzero coefficient of a linear equation — lets
-- "Since b ≠ 0 and a + b * t₁ = a + b * t₂ we get that t₁ - t₂ = 0"
-- work directly (injectivity of t ↦ a + b * t).
lemma sub_eq_zero_of_linear_eq {a b t₁ t₂ : ℝ} (hb : b ≠ 0)
    (h : a + b * t₁ = a + b * t₂) : t₁ - t₂ = 0 := by
  have hbt : b * t₁ = b * t₂ := by linarith
  have := mul_left_cancel₀ hb hbt
  linarith

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

-- Pair-value contradiction bridges: two different values for the same x are
-- contradictory (used to show e.g. {0, 2} ∩ {1, 3} = ∅ by case analysis).
lemma zero_one_false {x : ℝ} (_ : x = 0) (_ : x = 1) : False := by linarith
lemma zero_three_false {x : ℝ} (_ : x = 0) (_ : x = 3) : False := by linarith
lemma two_one_false {x : ℝ} (_ : x = 2) (_ : x = 1) : False := by linarith
lemma two_three_false {x : ℝ} (_ : x = 2) (_ : x = 3) : False := by linarith

-- ══════════════════════════════════════════════════════════════
-- § Interval arithmetic helpers
-- ══════════════════════════════════════════════════════════════

-- x ≤ y and 0 < z implies x < y + z (used when the right endpoint includes a positive offset).
lemma lt_add_pos_right {x y z : ℝ} (h1 : x ≤ y) (h2 : 0 < z) : x < y + z := by linarith

-- x ≤ y - z and 0 < z implies x < y (used to discharge x < 1 from x ≤ 1 - 1/n and 1/n > 0).
lemma le_sub_pos_lt {x y z : ℝ} (h1 : x ≤ y - z) (h2 : 0 < z) : x < y := by linarith

-- x < 1 + z and z < x - 1 is contradictory (linarith: x < 1 + (x-1) = x).
lemma lt_add_lt_self_false {x z : ℝ} (h1 : x < 1 + z) (h2 : z < x - 1) : False := by linarith

-- ══════════════════════════════════════════════════════════════
-- § Archimedean bridges
-- ══════════════════════════════════════════════════════════════

-- x > 1 gives x - 1 > 0, feeding the archimedean step below.
lemma x_gt_one_imp {x : ℝ} (h : x > 1) : x - 1 > 0 := by linarith

-- Above any real number there is a natural number, and it may be taken to be at
-- least 1 (so that dividing by it is harmless).  This is the form used to pick a
-- threshold instead of a ceiling function: "pick an integer M ≥ 1 with M > …".
lemma archimedean_nat (x : ℝ) : ∃ M : ℕ, M ≥ 1 ∧ (M : ℝ) > x := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max x 1)
  refine ⟨M, ?_, lt_of_le_of_lt (le_max_left _ _) hM⟩
  have h1 : (1 : ℝ) ≤ M := le_of_lt (lt_of_le_of_lt (le_max_right x 1) hM)
  exact_mod_cast h1

-- For positive x there is a natural k ≥ 1 with k > 1/x (the bound `1 / x` is
-- what the interval sheets need; convergence sheets use `archimedean_nat`).
lemma archimedean_bridge_k {x : ℝ} (_hx : x > 0) : ∃ k : ℕ, k ≥ 1 ∧ k > 1 / x :=
  archimedean_nat (1 / x)

-- Specialisation to 1 - x for x < 1, as it appears in union-of-intervals exercises.
lemma limit_archimedean_bridge_k {x : ℝ} (hx : x < 1) : ∃ k : ℕ, k ≥ 1 ∧ k > 1 / (1 - x) := by
  have : 1 - x > 0 := by linarith
  exact archimedean_bridge_k this

-- n > 1/x turns into 1/n < x (for positive x).
lemma inv_lt_bridge {x n : ℝ} (hx : x > 0) (h : n > 1 / x) : 1 / n < x := by
  have h1 : 1 / x > 0 := one_div_pos.mpr hx
  have hn : n > 0 := by linarith
  have h2 : 1 / n < 1 / (1 / x) := (one_div_lt_one_div hn h1).mpr h
  rwa [one_div_one_div] at h2

-- Specialisation to x < 1: n > 1/(1-x) turns into 1/n < 1 - x.
lemma limit_inv_lt_bridge {n : ℕ} {x : ℝ} (hx : x < 1) (h : n > 1 / (1 - x)) : 1 / n < 1 - x := by
  have h1 : 1 - x > 0 := by linarith
  exact inv_lt_bridge h1 h

-- Helpers: a natural n ≥ 1 is positive as a real, and so is 1/n.
lemma cast_pos_bridge {n : ℕ} (h : n ≥ 1) : (n : ℝ) > 0 := by
  have : n ≠ 0 := by omega
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero this)

lemma inv_pos_bridge {n : ℕ} (h : n ≥ 1) : 1 / (n : ℝ) > 0 := one_div_pos.mpr (cast_pos_bridge h)

-- x ≤ 1 stays below the growing bound 1 + 1/n.
lemma growing_bound_bridge {x : ℝ} {n : ℕ} (h1 : n ≥ 1) (h2 : x ≤ 1) :
    x < 1 + 1 / n := by linarith [inv_pos_bridge h1]

-- x below the shrinking bound 1 - 1/n stays below 1.
lemma shrinking_bound_bridge {x : ℝ} {n : ℕ} (h1 : n ≥ 1) (h2 : x ≤ 1 - 1 / n) :
    x < 1 := by linarith [inv_pos_bridge h1]

-- ══════════════════════════════════════════════════════════════
-- § Indexed interval families
-- ══════════════════════════════════════════════════════════════

-- Instantiate membership in ⋂ (m ≥ 1), [0, 1 + 1/m) at a particular n ≥ 1.
lemma mem_iInter_Ico {x : ℝ} {n : ℕ}
    (h1 : x ∈ ⋂ (m : ℕ) (_ : m ≥ 1), Set.Ico (0:ℝ) (1 + 1 / m))
    (h2 : n ≥ 1) : x ∈ Set.Ico (0:ℝ) (1 + 1 / n) :=
  Set.mem_iInter₂.mp h1 n h2

-- Instantiate the same intersection at n = 1.
lemma mem_Ico_one {x : ℝ}
    (h : x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), Set.Ico (0:ℝ) (1 + 1 / n)) :
    x ∈ Set.Ico (0:ℝ) (1 + 1 / 1) := by
  have h1 : (1:ℕ) ≥ 1 := by omega
  simpa using Set.mem_iInter₂.mp h 1 h1

-- Intro for the intersection from the pointwise statement.
lemma mem_iInter_Ico_forall {x : ℝ}
    (h : ∀ n : ℕ, n ≥ 1 → x ∈ Set.Ico (0:ℝ) (1 + 1 / n)) :
    x ∈ ⋂ (n : ℕ) (_ : n ≥ 1), Set.Ico (0:ℝ) (1 + 1 / n) :=
  Set.mem_iInter₂.mpr h

-- Elim for membership in ⋃ (n ≥ 1), [0, 1 - 1/n].
lemma iUnion_extract_Icc {x : ℝ}
    (h : x ∈ ⋃ (n : ℕ) (_ : n ≥ 1), Set.Icc (0:ℝ) (1 - 1 / n)) :
    ∃ n : ℕ, n ≥ 1 ∧ x ∈ Set.Icc (0:ℝ) (1 - 1 / n) := by
  rcases Set.mem_iUnion₂.mp h with ⟨n, hn, hx⟩
  exact ⟨n, hn, hx⟩

-- Intro for the same union from a witness.
lemma mem_iUnion_Icc {x : ℝ} {n : ℕ}
    (h1 : n ≥ 1) (h2 : x ∈ Set.Icc (0:ℝ) (1 - 1 / n)) :
    x ∈ ⋃ (n : ℕ) (_ : n ≥ 1), Set.Icc (0:ℝ) (1 - 1 / n) :=
  Set.mem_iUnion₂.mpr ⟨n, h1, h2⟩

-- Instantiate ⋂ n, [0, n) over ℕ at n = 0.
lemma mem_iInter_nat_bridge {x : ℕ}
    (h : x ∈ ⋂ n : ℕ, Set.Iio (n:ℕ)) :
    x ∈ Set.Iio (0:ℕ) := Set.mem_iInter.mp h 0

-- ══════════════════════════════════════════════════════════════
-- § Natural number helpers
-- ══════════════════════════════════════════════════════════════

-- x : ℕ is a member of Set.univ (trivially, used to discharge membership goals).
lemma nat_mem_univ (x : ℕ) : x ∈ (Set.univ : Set ℕ) := Set.mem_univ x

-- x : ℕ satisfies x ≥ 0 (trivially true for ℕ).
lemma nat_mem_ge_zero (x : ℕ) : x ∈ {k : ℕ | k ≥ 0} := Nat.zero_le x

-- x ≥ x + 1 is impossible for ℕ.
lemma nat_ge_succ_false {x : ℕ} (h : x ≥ x + 1) : False := by omega

-- x < 0 is impossible for ℕ.
lemma nat_lt_zero_false {x : ℕ} (h : x < 0) : False := by omega

-- max i j ≥ i and max i j ≥ j (for ℕ, used in indexed-operation exercises).
lemma nat_max_ge_left (i j : ℕ) : max i j ≥ i := le_max_left i j
lemma nat_max_ge_right (i j : ℕ) : max i j ≥ j := le_max_right i j
