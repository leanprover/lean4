/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
definition map (A B : Type) := A → option B

namespace map
variables {A B : Type}
open tactic

definition empty : map A B :=
λ a, none

definition lookup (k : A) (m : map A B) : option B :=
m k

theorem ext (m₁ m₂ : map A B) : (∀ a, lookup a m₁ = lookup a m₂) → m₁ = m₂ :=
funext

theorem lookup_empty (k : A) : lookup k (empty : map A B) = none :=
rfl

variable [decidable_eq A]

definition insert (k : A) (v : B) (m : map A B) : map A B :=
λ a, if a = k then some v else m a

theorem lookup_insert (k : A) (v : B) (m : map A B) : lookup k (insert k v m) = some v :=
by unfold ["map" <.> "insert", "map" <.> "lookup"] >> dsimp >> rewrite "if_pos" >> reflexivity

theorem lookup_insert_of_ne {k₁ k₂ : A} (v : B) (m : map A B) : k₁ ≠ k₂ → lookup k₁ (insert k₂ v m) = lookup k₁ m :=
by intros >> unfold ["map" <.> "insert", "map" <.> "lookup"] >> dsimp >> rewrite "if_neg" >> assumption

definition erase (k : A) (m : map A B) : map A B :=
λ a, if a = k then none else m a

theorem lookup_erase (k : A) (v : B) (m : map A B) : lookup k (erase k m) = none :=
by unfold ["map" <.> "erase", "map" <.> "lookup"] >> dsimp >> rewrite "if_pos" >> reflexivity

theorem lookup_erase_of_ne {k₁ k₂ : A} (v : B) (m : map A B) : k₁ ≠ k₂ → lookup k₁ (erase k₂ m) = lookup k₁ m :=
by intros >> unfold ["map" <.> "erase", "map" <.> "lookup"] >> dsimp >> rewrite "if_neg" >> assumption

theorem erase_empty (k : A) : erase k empty = (empty : map A B) :=
funext (λ a, by unfold ["map" <.> "erase", "map" <.> "empty"] >> rewrite "if_t_t")

theorem erase_insert {k : A} {m : map A B} (v : B) : lookup k m = none → erase k (insert k v m) = m :=
assume h, funext (λ a, decidable.by_cases
  (suppose a = k, by get_local "this" >>= subst >> unfold ["map" <.> "erase", "map" <.> "insert"] >> rewrite "if_pos" >> symmetry >> assumption >> reflexivity)
  (suppose a ≠ k, by unfold ["map" <.> "erase", "map" <.> "insert"] >> rewrite "if_neg" >> dsimp >> rewrite "if_neg" >> repeat assumption))

end map
