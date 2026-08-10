/-
  Generic function lemmas and notation for Waterproof exercise sheets.

  Covers: f(x) application notation, injectivity/surjectivity/bijectivity
  phrases, relation phrases (antisymmetric/transitive), inverse-function
  phrases, equality bridges, and image/preimage lemmas. Works for any function f : X → Y; no domain-specific mathematics
  required. Register lemmas in each sheet's doc block with
  addAnonymousGoalSplittingLemma.
-/

import Verbose.English.All

-- ══════════════════════════════════════════════════════════════
-- § Notation: f(x) for function application
-- ══════════════════════════════════════════════════════════════
-- Students write f(x) on paper. This notation lets Lean accept f(x)
-- as an alias for f x throughout exercise sheets.
--
-- Works in: Given:, Conclusion:, proof bodies
-- Limitation: Does NOT work in Assume: clauses (Verbose parser limitation)
notation:max g "(" y ")" => g y

-- ══════════════════════════════════════════════════════════════
-- § Notation: injectivity, surjectivity, bijectivity
-- ══════════════════════════════════════════════════════════════

notation:50 f " is injective" => Function.Injective f
notation:50 f " is surjective" => Function.Surjective f
notation:50 f " is bijective" => Function.Bijective f

-- ══════════════════════════════════════════════════════════════
-- § Relations: antisymmetry, transitivity
-- ══════════════════════════════════════════════════════════════

-- Definition 5.1.30 (Lecture 9)
def antisymmetric {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b : X, R a b → R b a → a = b

-- Definition 5.1.36 (Lecture 9)
def transitive {X : Type} (R : X → X → Prop) : Prop :=
  ∀ a b c : X, R a b → R b c → R a c

notation:50 R " is antisymmetric" => antisymmetric R
notation:50 R " is transitive" => transitive R

-- ══════════════════════════════════════════════════════════════
-- § Notation: inverse functions
-- ══════════════════════════════════════════════════════════════
-- The word "a" cannot appear in a `notation` (it would become a reserved
-- token and break variables named `a`), so these phrases use `syntax` +
-- `macro_rules`, where Verbose keeps "a" non-reserved.

syntax:50 term:51 " is a left inverse of " term:51 : term
macro_rules
  | `($g is a left inverse of $f) => `(Function.LeftInverse $g $f)

syntax:50 term:51 " is a right inverse of " term:51 : term
macro_rules
  | `($g is a right inverse of $f) => `(Function.RightInverse $g $f)

syntax:50 term:51 " has a left inverse" : term
macro_rules
  | `($f has a left inverse) => `(∃ g, Function.LeftInverse g $f)

syntax:50 term:51 " has a right inverse" : term
macro_rules
  | `($f has a right inverse) => `(∃ g, Function.RightInverse g $f)

notation:50 g " is an inverse of " f:51 =>
  Function.LeftInverse g f ∧ Function.RightInverse g f

-- Pretty-print LeftInverse/RightInverse back to the phrases above
open Lean PrettyPrinter in
@[app_unexpander Function.LeftInverse]
private def unexpandLeftInverse : Unexpander
  | `($_ $g $f) => `($g is a left inverse of $f)
  | _ => throw ()

open Lean PrettyPrinter in
@[app_unexpander Function.RightInverse]
private def unexpandRightInverse : Unexpander
  | `($_ $g $f) => `($g is a right inverse of $f)
  | _ => throw ()

-- ══════════════════════════════════════════════════════════════
-- § Equality bridges
-- ══════════════════════════════════════════════════════════════

-- Applying a function to both sides of an equality — lets
-- "Since a = b we get that g(a) = g(b)" work directly.
lemma apply_eq_of_eq {X Y : Type} (g : X → Y) {a b : X}
    (h : a = b) : g a = g b := by rw [h]

-- Transitivity of equality.
lemma eq_trans_bridge {X : Type} {a b c : X}
    (h₁ : a = b) (h₂ : b = c) : a = c := h₁.trans h₂

-- Two elements with equal images under equal names are equal — lets
-- "Since G(F(a)) = a, G(F(b)) = b and G(F(a)) = G(F(b))
--  we conclude that a = b" work directly.
lemma eq_of_eq_of_eq {X : Type} {u v a b : X}
    (h₁ : u = a) (h₂ : v = b) (h₃ : u = v) : a = b := by rw [← h₁, ← h₂, h₃]

-- ══════════════════════════════════════════════════════════════
-- § Injectivity, surjectivity, bijectivity
-- ══════════════════════════════════════════════════════════════

-- A bijective function is injective.
lemma injective_of_bijective {X Y : Type} {f : X → Y}
    (h : Function.Bijective f) : Function.Injective f := h.1

-- A bijective function is surjective.
lemma surjective_of_bijective {X Y : Type} {f : X → Y}
    (h : Function.Bijective f) : Function.Surjective f := h.2

-- Converse: injective and surjective together give bijective.
lemma bijective_of_injective_surjective {X Y : Type} {f : X → Y}
    (h₁ : Function.Injective f) (h₂ : Function.Surjective f) :
    Function.Bijective f := ⟨h₁, h₂⟩

-- ══════════════════════════════════════════════════════════════
-- § Images
-- ══════════════════════════════════════════════════════════════

-- x ∈ A implies f(x) ∈ f '' A — lets
-- "Since x ∈ A we conclude that f(x) ∈ f '' A" work directly.
lemma image_of_mem {X Y : Type} {f : X → Y} {A : Set X} {x : X}
    (h : x ∈ A) : f x ∈ f '' A :=
  Set.mem_image_of_mem f h

-- ══════════════════════════════════════════════════════════════
-- § Preimages
-- ══════════════════════════════════════════════════════════════
-- No bridge lemmas needed: x ∈ f ⁻¹' V unfolds definitionally to f(x) ∈ V,
-- so Verbose closes both directions without help (verified by removal in
-- Lecture5/sheet2_preimage).
