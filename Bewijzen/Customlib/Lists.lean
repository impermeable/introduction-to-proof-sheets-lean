/-
  Topic-based lemma lists for Verbose Lean exercise sheets.

  These named lists use VerboseLean's DeclListExtension infrastructure so that
  `addAnonymousGoalSplittingLemma` and `configureAnonymousCaseSplittingLemmas`
  can reference them by name. Each sheet then composes its configuration by
  referencing the topic lists it needs instead of listing lemmas one by one.

  See .lake/packages/verbose-lean4/Verbose/Infrastructure/Extension.lean for the
  underlying mechanism.
-/

import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Reals

-- ══════════════════════════════════════════════════════════════
-- § Case splitting: classical logic
-- ══════════════════════════════════════════════════════════════

-- Classical excluded middle, used in every sheet.
-- Sheets add further case-splitting lemmas via configureAnonymousCaseSplittingLemmas.
AnonymousCaseSplittingLemmasList caseSplittingClassical := Classical.em

-- Real number dichotomies used for case splitting.
-- (Separate from realDichotomies which is a GoalSplitting list.)
AnonymousCaseSplittingLemmasList caseSplittingRealDichotomies :=
  ge_or_le_zero le_or_gt_zero gt_zero_or_le_zero lt_or_ge_one

-- ══════════════════════════════════════════════════════════════
-- § Order theory (basic transitivity and comparison)
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList orderTheory :=
  lt_of_lt_of_le lt_of_le_of_lt le_trans lt_trans LT.lt.false lt_le_imp_le

-- ══════════════════════════════════════════════════════════════
-- § Real numbers (dichotomies and sign arithmetic)
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList realDichotomies :=
  ge_or_le_zero le_or_gt_zero gt_zero_or_le_zero lt_or_ge_one

AnonymousGoalSplittingLemmasList realSignArithmetic :=
  gt_zero_and_lt_one_to_Ioo root_gt_zero mul_self_ge_self_of_ge_one
  mul_self_ge_self_of_le_zero ge_and_lt_real_false bound_contra
  multiplication_dichotomy_bridge

-- ══════════════════════════════════════════════════════════════
-- § Interval properties (membership and subset)
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList intervalMembership :=
  mem_Icc_left mem_Ico_self mem_Ioc_self midpoint_mem_Ioo mem_Ioo_extract
  Icc_R_intro sq_le_one_of_abs sq_le_one_imp_mul_nonneg

AnonymousGoalSplittingLemmasList intervalSubset :=
  Ico_sub_Ioc_forward Ico_sub_Ioc_forward_b_le_d' mem_Ico_self

-- ══════════════════════════════════════════════════════════════
-- § Set theory (subset and empty set)
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList subsetTheory := Set.Subset.antisymm

AnonymousGoalSplittingLemmasList emptySet :=
  mem_empty_contra set_eq_empty_of_forall_not_mem false_of_mem_empty_set

-- ══════════════════════════════════════════════════════════════
-- § Pair sets
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList pairSets :=
  mem_pair_cases mem_pair_intro_left mem_pair_intro_right

-- ══════════════════════════════════════════════════════════════
-- § De Morgan bridges
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList deMorgan :=
  de_morgan_bridge contradiction_from_dm

-- ══════════════════════════════════════════════════════════════
-- § Square root and quadratic
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList squareRoot :=
  sqrt_pos_and_sq eq_sqrt_of_pos_sq quad_root neg_a_is_root sq_sum_zero_imp
