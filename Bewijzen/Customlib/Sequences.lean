/-
  Sequences of real numbers for Waterproof exercise sheets.

  Covers: the definition of convergence and the `converges to` / `converges`
  phrases, the reciprocal tail estimates that close the last lines of an
  epsilon-N estimate chain, and the closed forms of `|u n - l|` for the standard
  worked sequences.

  The Archimedean step that produces the threshold `M` lives in
  `Bewijzen.Customlib.Reals` (`archimedean_nat`), as does the `unop%` elaboration
  of `|…|` that lets students write the bars without casts.

  Register lemmas in each sheet's doc block with `addAnonymousGoalSplittingLemma`
  / `addAnonymousComputeLemma`, and declare the definitions unfoldable there with
  `configureUnfoldableDefs`; no registrations live here.
-/

import Verbose.English.All
import Bewijzen.Customlib.Reals

-- ══════════════════════════════════════════════════════════════
-- § Convergence
-- ══════════════════════════════════════════════════════════════

-- A sequence `u` converges to `l` when it gets arbitrarily close to `l`.
-- The inequality is strict: the estimate chains on the sheets end at `… < ε`,
-- and Lean's `calc` needs the composed relation to be the one in the goal.
def converges_to (u : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

-- A sequence converges when it has some limit.
def IsConvergent (u : ℕ → ℝ) := ∃ l : ℝ, converges_to u l

notation:50 u:80 " converges to " l => converges_to u l
notation:50 u:80 " converges"        => IsConvergent u

-- ══════════════════════════════════════════════════════════════
-- § Reciprocal tail estimates
-- ══════════════════════════════════════════════════════════════
-- Each states one line of an estimate chain: past the threshold `M`, the
-- reciprocal of a growing quantity is at most `1 / M`.  `M ≥ 1` is what makes
-- dividing by `M` harmless — in Lean `1 / 0 = 0`, so the estimates are false
-- at `M = 0`.

-- From `M ≤ n` between naturals with `M ≥ 1`.
lemma one_div_le_one_div_nat {M n : ℕ} (hM : M ≥ 1) (hn : n ≥ M) :
    1 / (n : ℝ) ≤ 1 / (M : ℝ) := by
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (cast_pos_bridge hM) hMn

-- Squares of naturals are ordered like the naturals themselves.
lemma one_div_sq_le_one_div_sq_nat {M n : ℕ} (hM : M ≥ 1) (hn : n ≥ M) :
    1 / ((n : ℝ) * n) ≤ 1 / ((M : ℝ) * M) := by
  have hM0 : (0 : ℝ) < M := cast_pos_bridge hM
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

-- `M * M` is at least `M`, so its reciprocal is at most `1 / M`.
lemma one_div_sq_le_one_div_nat {M : ℕ} (hM : M ≥ 1) :
    1 / ((M : ℝ) * M) ≤ 1 / (M : ℝ) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  exact one_div_le_one_div_of_le (by linarith) (by nlinarith)

-- Powers of 2 are ordered like their exponents.
lemma one_div_two_pow_le_two_pow_nat {M n : ℕ} (hn : n ≥ M) :
    1 / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ M :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hn)

-- `2 ^ M` is at least `M`, so its reciprocal is at most `1 / M`.
lemma one_div_two_pow_le_one_div_nat {M : ℕ} (hM : M ≥ 1) :
    1 / (2 : ℝ) ^ M ≤ 1 / (M : ℝ) := by
  have hMpow : (M : ℝ) ≤ (2 : ℝ) ^ M := by
    calc (M : ℝ) ≤ ((2 ^ M : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_lt M.lt_two_pow_self
      _ = (2 : ℝ) ^ M := by push_cast; ring
  exact one_div_le_one_div_of_le (cast_pos_bridge hM) hMpow

-- `n + 2` is at least `M`.
lemma one_div_add_two_le_one_div_nat {M n : ℕ} (hM : M ≥ 1) (hn : n ≥ M) :
    1 / ((n : ℝ) + 2) ≤ 1 / (M : ℝ) := by
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (cast_pos_bridge hM) (by linarith)

-- ══════════════════════════════════════════════════════════════
-- § Removing absolute value signs
-- ══════════════════════════════════════════════════════════════
-- The last step of a chain whose limit is `0`: the quantity inside the bars is
-- already nonnegative.  Registered on the sheets with `addAnonymousComputeLemma`,
-- so that `by computation` performs them.

lemma abs_one_div_nat (n : ℕ) : |1 / (n : ℝ)| = 1 / (n : ℝ) :=
  abs_of_nonneg (by positivity)

lemma abs_one_div_sq_nat (n : ℕ) :
    |1 / ((n : ℝ) * n)| = 1 / ((n : ℝ) * n) :=
  abs_of_nonneg (by positivity)

lemma abs_one_div_two_pow (n : ℕ) :
    |1 / (2 : ℝ) ^ n| = 1 / (2 : ℝ) ^ n :=
  abs_of_nonneg (by positivity)

-- ══════════════════════════════════════════════════════════════
-- § Distance to the limit, for the standard worked sequences
-- ══════════════════════════════════════════════════════════════
-- When the limit is not `0`, the absolute value hides a subtraction of
-- fractions, and rewriting `|u n - l|` into a closed form is the first step of
-- the chain.  Also compute lemmas.

-- `n ↦ 3 * n / (2 * n + 1)` and its limit `3 / 2`.
lemma abs_sub_three_div_two (n : ℕ) :
    |(3 * (n : ℝ)) / (2 * n + 1) - 3 / 2| = 3 / (2 * (2 * (n : ℝ) + 1)) := by
  rw [show (3 * (n : ℝ)) / (2 * n + 1) - 3 / 2 = -(3 / (2 * (2 * (n : ℝ) + 1))) by
    have : (2 * (n : ℝ) + 1) > 0 := by positivity
    field_simp; ring]
  rw [abs_neg, abs_of_pos (by positivity)]

-- `n ↦ 3 + (n - 1) / (2 * n + 1)` and its limit `7 / 2`, in two steps: first
-- cancel the `3` against the `7 / 2`, then use the lemma below.
lemma abs_sub_seven_div_two_cancel (n : ℕ) :
    |3 + ((n : ℝ) - 1) / (2 * n + 1) - 7 / 2|
      = |((n : ℝ) - 1) / (2 * n + 1) - 1 / 2| := by
  congr 1; ring

lemma abs_sub_one_div_two (n : ℕ) :
    |((n : ℝ) - 1) / (2 * n + 1) - 1 / 2| = 3 / (2 * (2 * (n : ℝ) + 1)) := by
  rw [show ((n : ℝ) - 1) / (2 * n + 1) - 1 / 2 = -(3 / (2 * (2 * (n : ℝ) + 1))) by
    have : (2 * (n : ℝ) + 1) > 0 := by positivity
    field_simp; ring]
  rw [abs_neg, abs_of_pos (by positivity)]

-- `n ↦ (n + 1) / (n + 2)` and its limit `1`, in two steps: first put the
-- subtraction over one denominator, then drop the absolute value signs.
lemma abs_sub_one_combine (n : ℕ) :
    |((n : ℝ) + 1) / (n + 2) - 1| = |(-1 : ℝ) / ((n : ℝ) + 2)| := by
  have : ((n : ℝ) + 2) > 0 := by positivity
  rw [show ((n : ℝ) + 1) / (n + 2) - 1 = (-1 : ℝ) / ((n : ℝ) + 2) by field_simp; ring]

lemma abs_neg_one_div_add_two (n : ℕ) :
    |(-1 : ℝ) / ((n : ℝ) + 2)| = 1 / ((n : ℝ) + 2) := by
  rw [show (-1 : ℝ) / ((n : ℝ) + 2) = -(1 / ((n : ℝ) + 2)) by ring]
  rw [abs_neg, abs_of_pos (by positivity)]

-- ══════════════════════════════════════════════════════════════
-- § Estimates for the threshold `M > 3 / (4 * ε)`
-- ══════════════════════════════════════════════════════════════
-- The two sequences above both reduce to `3 / (2 * (2 * n + 1))`, which is
-- estimated in three steps down to `ε`.

-- `2 * (2 * n + 1)` is at least `4 * n`.
lemma three_div_two_mul_le_three_div_four_mul {M n : ℕ} (hM : M ≥ 1) (hn : n ≥ M) :
    3 / (2 * (2 * (n : ℝ) + 1)) ≤ 3 / (4 * (n : ℝ)) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

-- The same reciprocal estimate, now between `n` and `M`.
lemma three_div_four_mul_le_three_div_four_mul {M n : ℕ} (hM : M ≥ 1) (hn : n ≥ M) :
    3 / (4 * (n : ℝ)) ≤ 3 / (4 * (M : ℝ)) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

-- The threshold `M > 3 / (4 * ε)` was chosen to make this true.
lemma three_div_four_mul_lt {M : ℕ} {ε : ℝ} (hε : ε > 0) (hM : (M : ℝ) > 3 / (4 * ε)) :
    3 / (4 * (M : ℝ)) < ε := by
  have h0 : (0 : ℝ) < 3 / (4 * ε) := by positivity
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 4 * M)]
  rw [gt_iff_lt, div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ε)] at hM
  linarith
