/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.logic

constant propext {a b : Prop} : (a ↔ b) → a = b

/- Additional congruence lemmas. -/
universes u v

lemma forall_congr_eq {a : Sort u} {p q : a → Prop} (h : ∀ x, p x = q x) : (∀ x, p x) = ∀ x, q x :=
propext (forall_congr (λ a, (h a)^.to_iff))

lemma imp_congr_eq {a b c d : Prop} (h₁ : a = c) (h₂ : b = d) : (a → b) = (c → d) :=
propext (imp_congr h₁^.to_iff h₂^.to_iff)

lemma imp_congr_ctx_eq {a b c d : Prop} (h₁ : a = c) (h₂ : c → (b = d)) : (a → b) = (c → d) :=
propext (imp_congr_ctx h₁^.to_iff (λ hc, (h₂ hc)^.to_iff))

lemma eq_true_intro {a : Prop} (h : a) : a = true :=
propext (iff_true_intro h)

lemma eq_false_intro {a : Prop} (h : ¬a) : a = false :=
propext (iff_false_intro h)
