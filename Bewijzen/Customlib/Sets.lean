/-
  Generic set-theory lemmas for Waterproof exercise sheets.

  Works for any type α; no domain-specific mathematics required.
  Register these in each sheet's doc block with addAnonymousGoalSplittingLemma.
-/

import Verbose.English.All

-- ══════════════════════════════════════════════════════════════
-- § Subset and set equality
-- ══════════════════════════════════════════════════════════════

-- Set equality from mutual inclusion, conjunction form.
-- Lets "It suffices to prove that A ⊆ B ∧ B ⊆ A" discharge A = B goals.
lemma set_eq_of_subset_conj {α : Type} {A B : Set α}
    (h : A ⊆ B ∧ B ⊆ A) : A = B :=
  Set.Subset.antisymm h.1 h.2

-- Transport membership along an equality of sets — lets
-- "Since A = B and x ∈ A we get that x ∈ B" work directly.
lemma mem_of_set_eq {U : Type} {A B : Set U} {x : U}
    (h : A = B) (hx : x ∈ A) : x ∈ B := h ▸ hx

-- Transport membership backwards along an equality of sets.
lemma mem_of_set_eq' {U : Type} {A B : Set U} {x : U}
    (h : A = B) (hx : x ∈ B) : x ∈ A := h ▸ hx

-- ══════════════════════════════════════════════════════════════
-- § Complement
-- ══════════════════════════════════════════════════════════════

-- An element outside the complement lies in the set.
lemma mem_of_not_mem_compl {U : Type} {A : Set U} {x : U}
    (h : x ∉ Aᶜ) : x ∈ A := by
  by_contra hx
  exact h hx

-- An element of the set lies outside the complement.
lemma not_mem_compl_of_mem {U : Type} {A : Set U} {x : U}
    (h : x ∈ A) : x ∉ Aᶜ := fun hc => hc h

-- ══════════════════════════════════════════════════════════════
-- § Empty set
-- ══════════════════════════════════════════════════════════════

def SetIsEmpty {U : Type} (X : Set U) : Prop :=
  ∀ _ ∈ X, False

-- The notation `X is empty` reads as `∀ x ∈ X, False`
namespace Bewijzen.EmptySetNotation
scoped notation:50 X " is empty" => SetIsEmpty X
end Bewijzen.EmptySetNotation

-- x ∈ ∅ implies False — lets "We conclude by contradicting x ∈ ∅" work directly.
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

-- ══════════════════════════════════════════════════════════════
-- § Propositional contradiction
-- ══════════════════════════════════════════════════════════════

lemma prop_and_neg_false {P : Prop} (h : P) (hn : ¬P) : False := hn h

-- From ¬(P ∧ Q) and P, obtain ¬Q.
lemma not_and_imp_not_right {P Q : Prop} (h1 : ¬(P ∧ Q)) (h2 : P) : ¬Q := by
  intro hq; exact h1 ⟨h2, hq⟩

-- ══════════════════════════════════════════════════════════════
-- § Set difference
-- ══════════════════════════════════════════════════════════════

lemma mem_diff_bridge {U : Type} {x : U} {A B : Set U} (h : x ∈ A \ B) :
    x ∈ A ∧ x ∉ B := h

lemma mem_diff_of_mem_not {U : Type} {x : U} {A B : Set U}
    (h1 : x ∈ A) (h2 : x ∉ B) : x ∈ A \ B := ⟨h1, h2⟩

-- ══════════════════════════════════════════════════════════════
-- § Negated membership (De Morgan bridges)
-- ══════════════════════════════════════════════════════════════

lemma not_inter_mem {U : Type} {x : U} {A B : Set U}
    (h : ¬ (x ∈ A ∧ x ∈ B)) : x ∉ A ∩ B := h

lemma not_mem_inter_of_not_left {U : Type} {x : U} {A B : Set U}
    (h1 : x ∉ A) : ¬ (x ∈ A ∧ x ∈ B) := by
  intro h
  rcases h with ⟨hA, hB⟩
  exact h1 hA

lemma not_mem_inter_of_not_right {U : Type} {x : U} {A B : Set U}
    (h1 : x ∉ B) : ¬ (x ∈ A ∧ x ∈ B) := by
  intro h
  rcases h with ⟨hA, hB⟩
  exact h1 hB

lemma not_mem_union_split {U : Type} {x : U} {A B : Set U}
    (h : x ∉ A ∪ B) : x ∉ A ∧ x ∉ B := by
  constructor
  · intro hA
    have : x ∈ A ∪ B := Or.inl hA
    exact h this
  · intro hB
    have : x ∈ A ∪ B := Or.inr hB
    exact h this

lemma not_union_mem {U : Type} {x : U} {A B : Set U}
    (h1 : x ∉ A) (h2 : x ∉ B) : ¬ (x ∈ A ∪ B) := by
  intro h
  rcases h with (hA | hB)
  · exact h1 hA
  · exact h2 hB

-- ══════════════════════════════════════════════════════════════
-- § Set union membership
-- ══════════════════════════════════════════════════════════════

lemma mem_union_left_bridge {U : Type} {x : U} {A B : Set U} (h : x ∈ A) : x ∈ A ∪ B := Or.inl h
lemma mem_union_right_bridge {U : Type} {x : U} {A B : Set U} (h : x ∈ B) : x ∈ A ∪ B := Or.inr h
