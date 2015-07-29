/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura

Classical proof that if f is injective, then f has a left inverse (if domain is not empty).
The proof uses the classical axioms: choice and excluded middle.
The excluded middle is being used "behind the scenes" to allow us to write the if-then-else expression
with (∃ a : A, f a = b).
-/
import logic.choice
open function

noncomputable definition mk_left_inv {A B : Type} [h : nonempty A] (f : A → B) : B → A :=
λ b : B, if ex : (∃ a : A, f a = b) then some ex else inhabited.value (inhabited_of_nonempty h)

theorem has_left_inverse_of_injective {A B : Type} {f : A → B} : nonempty A → injective f → has_left_inverse f :=
assume h : nonempty A,
assume inj  : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂,
let  finv : B → A := mk_left_inv f in
have linv : left_inverse finv f, from
  λ a,
    assert ex : ∃ a₁ : A, f a₁ = f a, from exists.intro a rfl,
    assert h₁ : f (some ex) = f a,    from !some_spec,
    begin
      esimp [mk_left_inv, compose, id],
      rewrite [dif_pos ex],
      exact (!inj h₁)
    end,
exists.intro finv linv
