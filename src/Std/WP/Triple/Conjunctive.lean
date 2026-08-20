/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Triple.Basic
public import Std.WP.Conjunctive
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Hoare triples for a conjunctive weakest precondition

Two specifications for one program `x` combine into a single specification when `wp x` is
conjunctive. `Triple.and` conjoins the two specifications. `Triple.mp` reads the second
specification as an implication and discharges its antecedent with the first. `Triple.observe`
runs a program `obs` for the sole purpose of learning a fact, then carries the fact into a
specification for a second program `prog`.
-/

namespace Std.WP

namespace Triple

universe u u' v v' w w'
variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type w'}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/--
Conjunction of two Hoare triple specifications for a program `x`. This theorem decomposes proofs:
prove unrelated facts about `x` separately, then combine them here.
-/
theorem and {x : Prog} [WPConjunctive x] {pre₁ pre₂ : Pred} {post₁ post₂ : Value → Pred}
    {epost₁ epost₂ : EPred}
    (h₁ : Triple x pre₁ post₁ epost₁) (h₂ : Triple x pre₂ post₂ epost₂) :
    Triple x (pre₁ ⊓ pre₂) (post₁ ⊓ post₂) (epost₁ ⊓ epost₂) :=
  ⟨PartialOrder.rel_trans (meet_mono h₁.le_wp h₂.le_wp)
    (WPConjunctive.wp_meet_wp_le post₁ post₂ epost₁ epost₂)⟩

/--
Modus ponens for two Hoare triple specifications of a program `x`. This theorem separates proofs.
Let `h₁` establish a basic postcondition `post₁` for `x`, and let `h₂` establish the advanced
postcondition `post₂` under the assumption `post₁`. Then `mp h₁ h₂` establishes `post₂` for `x`.
-/
theorem mp {x : Prog} [WPConjunctive x]
    [Heyting Pred] [Heyting EPred]
    {pre₁ pre₂ : Pred} {post₁ post₂ : Value → Pred} {epost₁ epost₂ : EPred}
    (h₁ : Triple x pre₁ post₁ epost₁)
    (h₂ : Triple x pre₂ (post₁ ⇨ post₂) (epost₁ ⇨ epost₂)) :
    Triple x (pre₁ ⊓ pre₂) (post₁ ⊓ post₂) (epost₁ ⊓ epost₂) :=
  ⟨PartialOrder.rel_trans (and h₁ h₂).le_wp
    (WP.wp_consequence_econs x _ _ _ _ meet_himp_le_meet meet_himp_le_meet)⟩

/--
Observe a fact about the state by running the program `obs`, then carry the fact into the proof
for the program `prog`. A specification for `prog` follows from the specification `h` for `obs`
with postcondition `post`, together with the specification `hgoal` deriving the goal
`wp prog post' epost'` from `post`. The premise `hp` restricts `obs` to observation: an assertion
that holds after a successful run of `obs` already holds before it.
-/
theorem observe {Prog' : Type u'} {Value' : Type v'} [WP Prog' Value' Pred EPred]
    [Heyting Pred] [Heyting EPred]
    {obs : Prog} [WPConjunctive obs] {prog : Prog'}
    {pre : Pred} {post : Value → Pred} {epost : EPred}
    {post' : Value' → Pred} {epost' : EPred}
    (hp : ∀ C : Pred, wp obs (fun _ => C) ⊥ ⊑ C)
    (h : Triple obs pre post epost)
    (hgoal : Triple obs pre (post ⇨ fun _ => wp prog post' epost') (epost ⇨ ⊥)) :
    Triple prog pre post' epost' :=
  ⟨PartialOrder.rel_trans (le_meet _ _ _ PartialOrder.rel_refl PartialOrder.rel_refl) <|
    PartialOrder.rel_trans (mp h hgoal).le_wp <|
      PartialOrder.rel_trans
        (WP.wp_consequence_econs obs _ _ _ _ (meet_le_right _ _) (meet_le_right _ _))
        (hp (wp prog post' epost'))⟩

end Triple

end Std.WP
