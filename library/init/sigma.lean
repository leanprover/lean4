/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes init.num init.wf init.logic

definition dpair := @sigma.mk
notation `Σ` binders `, ` r:(scoped P, sigma P) := r

universe variables u v

lemma ex_of_sig {A : Type u} {P : A → Prop} : (Σ x, P x) → ∃ x, P x
| ⟨x, hx⟩ := ⟨x, hx⟩

namespace sigma
  notation `pr₁`  := pr1
  notation `pr₂`  := pr2

  namespace ops
  postfix `.1`:(max+1) := pr1
  postfix `.2`:(max+1) := pr2
  end ops

  open ops

  variables {A : Type u} {B : A → Type v}

  protected theorem eq : ∀ {p₁ p₂ : Σ a : A, B a} (H₁ : p₁.1 = p₂.1), (eq.rec_on H₁ p₁.2 : B p₂.1) = p₂.2 → p₁ = p₂
  | ⟨a, b⟩ ⟨.a, .b⟩ rfl rfl := rfl

end sigma
