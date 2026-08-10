/-
  Topic-based lemma lists for Verbose Lean exercise sheets.

  These named lists use VerboseLean's DeclListExtension infrastructure so that
  `addAnonymousGoalSplittingLemma` and `configureAnonymousCaseSplittingLemmas`
  can reference them by name. Each sheet then composes its configuration by
  referencing the topic lists it needs instead of listing lemmas one by one.

  See .lake/packages/verbose-lean4/Verbose/Infrastructure/Extension.lean for the
  underlying mechanism.
-/

import Bewijzen.Customlib.Functions
import Bewijzen.Customlib.Sets
import Bewijzen.Customlib.Reals
import Bewijzen.Customlib.Rational

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

AnonymousGoalSplittingLemmasList orderAntisymmetry := antisymm_le

-- ══════════════════════════════════════════════════════════════
-- § Rational numbers (arithmetic closure and transfer)
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList rationalArithmetic :=
  rational_add rational_sub rational_mul rational_neg rational_of_eq

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

AnonymousGoalSplittingLemmasList intervalArithmetic :=
  lt_add_pos_right le_sub_pos_lt lt_add_lt_self_false

AnonymousGoalSplittingLemmasList natArithmetic :=
  nat_mem_univ nat_mem_ge_zero nat_ge_succ_false nat_lt_zero_false
  nat_max_ge_left nat_max_ge_right

-- ══════════════════════════════════════════════════════════════
-- § Set theory (subset and empty set)
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList subsetTheory := Set.Subset.antisymm set_eq_of_subset_conj

AnonymousGoalSplittingLemmasList setEqualityTransport := mem_of_set_eq mem_of_set_eq'

AnonymousGoalSplittingLemmasList complementMembership :=
  mem_of_not_mem_compl not_mem_compl_of_mem

AnonymousGoalSplittingLemmasList emptySet :=
  mem_empty_contra set_eq_empty_of_forall_not_mem false_of_mem_empty_set

AnonymousGoalSplittingLemmasList unionMembership :=
  mem_union_left_bridge mem_union_right_bridge

AnonymousGoalSplittingLemmasList setDifference :=
  mem_diff_bridge mem_diff_of_mem_not

AnonymousGoalSplittingLemmasList negatedMembership :=
  not_and_imp_not_right not_inter_mem not_mem_inter_of_not_left
  not_mem_inter_of_not_right not_mem_union_split not_union_mem

-- ══════════════════════════════════════════════════════════════
-- § Function images
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList imageMembership := image_of_mem

-- ══════════════════════════════════════════════════════════════
-- § Equality bridges
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList equalityBridges :=
  apply_eq_of_eq eq_trans_bridge eq_of_eq_of_eq

-- ══════════════════════════════════════════════════════════════
-- § Injectivity, surjectivity, bijectivity
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList bijectivity :=
  injective_of_bijective surjective_of_bijective bijective_of_injective_surjective

-- ══════════════════════════════════════════════════════════════
-- § Linear equations
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList linearEquations := sub_eq_zero_of_linear_eq

-- ══════════════════════════════════════════════════════════════
-- § Pair sets
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList pairSets :=
  mem_pair_cases mem_pair_intro_left mem_pair_intro_right

AnonymousGoalSplittingLemmasList pairValueContradictions :=
  zero_one_false zero_three_false two_one_false two_three_false

-- ══════════════════════════════════════════════════════════════
-- § Single intervals
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList singleInterval :=
  isSingleInterval_of_eq_Icc isSingleInterval_of_eq_Ico

-- ══════════════════════════════════════════════════════════════
-- § Archimedean property and indexed interval families
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList archimedean :=
  x_gt_one_imp archimedean_bridge_k limit_archimedean_bridge_k
  inv_lt_bridge limit_inv_lt_bridge growing_bound_bridge shrinking_bound_bridge

AnonymousGoalSplittingLemmasList indexedIntervals :=
  mem_iInter_Ico mem_Ico_one mem_iInter_Ico_forall
  iUnion_extract_Icc mem_iUnion_Icc mem_iInter_nat_bridge mem_Icc_bridge

-- ══════════════════════════════════════════════════════════════
-- § De Morgan bridges
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList deMorgan :=
  de_morgan_bridge contradiction_from_dm

-- ══════════════════════════════════════════════════════════════
-- § Square root and quadratic
-- ══════════════════════════════════════════════════════════════

AnonymousGoalSplittingLemmasList squareRoot :=
  sqrt_pos_and_sq eq_sqrt_of_pos_sq neg_a_is_root
  pos_sq zero_of_sq_eq_zero nonneg_sq nonneg_add_pos eq_and_gt_false
  factors_zero
