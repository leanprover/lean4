/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import data.encodable
open nat encodable

/-
In mathematics, the axiom of dependent choice is a weak form of the axiom of choice that is
sufficient to develop most of real analysis. See http://en.wikipedia.org/wiki/Axiom_of_dependent_choice.
We can state it as follows:
-/
definition dependent_choice {A : Type} (R : A → A → Prop) :=
(∀ a : A, ∃ b : A, R a b) → (∀ a : A, ∃ f : nat → A, f 0 = a ∧ ∀ n, R (f n) (f (n+1)))

/-
If A is an encodable type, and R is a decidable relation, we can prove (dependent_choice R) using the
constructive choice function "choose"
-/
section depchoice
  parameters {A : Type} {R : A → A → Prop}
  parameters [encA : encodable A] [decR : decidable_rel R]
  include encA decR

  local infix `~` := R

  private definition f_aux (a : A) (H : ∀ a, ∃ b, a ~ b) : nat → A
  | 0     := a
  | (n+1) := choose (H (f_aux n))

  theorem dependent_choice_of_encodable_of_decidable : dependent_choice R :=
  assume H : ∀ a, ∃ b, a ~ b,
  take   a : A,
  let    f : nat → A := f_aux a H in
  have   f_zero : f 0 = a,            from rfl,
  have   R_seq  : ∀ n, f n ~ f (n+1), from
    take n, show f n ~ choose (H (f n)), from !choose_spec,
  exists.intro f (and.intro f_zero R_seq)

  /-
  The following slightly stronger version can be proved, where we also "return" the constructed function f.
  We just have to use Σ instead of ∃, and use Σ-constructor instead of exists.intro.
  Recall that ⟨f, H⟩ is notation for (sigma.mk f H)
  -/
  theorem stronger_dependent_choice_of_encodable_of_decidable
          : (∀ a, ∃ b, R a b) → (∀ a, Σ f, f 0 = a ∧ ∀ n, f n ~ f (n+1))  :=
  assume H : ∀ a, ∃ b, a ~ b,
  take   a : A,
  let    f : nat → A := f_aux a H in
  have   f_zero : f 0 = a,            from rfl,
  have   R_seq  : ∀ n, f n ~ f (n+1), from
    take n, show f n ~ choose (H (f n)), from !choose_spec,
  ⟨f, and.intro f_zero R_seq⟩

end depchoice

/-
If we encode dependent_choice using Σ instead of ∃.
Then, we can prove this version without using any extra hypothesis (e.g., A is encodable or R is decidable).
The function f can be constructed directly from the hypothesis: ∀ a : A, Σ b : A, R a b
because Σ "carries" the witness 'b'. That is, we don't have to search for anything using "choose".
-/
open sigma.ops

section sigma_depchoice
  parameters {A : Type} {R : A → A → Prop}
  local infix `~` := R

  private definition f_aux (a : A) (H : ∀ a, Σ b, a ~ b) : nat → A
  | 0     := a
  | (n+1) := (H (f_aux n)).1

  theorem sigma_dependent_choice : (∀ a, Σ b, R a b) → (∀ a, Σ f, f 0 = a ∧ ∀ n, f n ~ f (n+1)) :=
  assume H : ∀ a, Σ b, a ~ b,
  take   a : A,
  let    f : nat → A := f_aux a H in
  have   f_zero : f 0 = a,            from rfl,
  have   R_seq  : ∀ n, f n ~ f (n+1), from take n, (H (f n)).2,
  ⟨f, and.intro f_zero R_seq⟩
end sigma_depchoice
