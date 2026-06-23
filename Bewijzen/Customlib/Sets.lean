/-
  Generic set-theory lemmas for Waterproof exercise sheets.

  Works for any type α; no domain-specific mathematics required.
  Register these in each sheet's doc block with addAnonymousGoalSplittingLemma.
-/

import Verbose.English.All

-- ══════════════════════════════════════════════════════════════
-- § Empty set
-- ══════════════════════════════════════════════════════════════

-- x ∈ ∅ implies False — lets "Since x ∈ ∅ we conclude that False" work directly.
lemma mem_empty_contra {α : Type} {x : α} (h : x ∈ (∅ : Set α)) : False := by
  simp [Set.mem_empty_iff_false] at h

-- A set equals ∅ when every membership assumption yields False.
-- Lets "It suffices to prove that ∀ x, x ∈ S → False" discharge S = ∅ goals.
lemma set_eq_empty_of_forall_not_mem {α : Type} {S : Set α}
    (h : ∀ x, x ∈ S → False) : S = ∅ :=
  Set.eq_empty_of_forall_notMem h

-- Membership in a known-empty set yields False.
lemma false_of_mem_empty_set {α : Type} {S : Set α} {x : α}
    (hS : S = ∅) (hx : x ∈ S) : False := by
  rw [hS] at hx; exact hx
