/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Additional congruence lemmas.
-/
prelude
import init.quot
universe variables u v

lemma forall_congr_eq {A : Type u} {p q : A → Prop} (h : ∀ a, p a = q a) : (∀ a, p a) = ∀ a, q a :=
propext (forall_congr (λ a, (h a)^.to_iff))

lemma imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
propext (imp_congr h₁^.to_iff h₂^.to_iff)
