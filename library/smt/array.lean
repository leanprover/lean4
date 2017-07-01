/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
namespace smt
universes u v
def array (α : Type u) (β : Type v) := α → β

variables {α : Type u} {β : Type v}
open tactic

def select (a : array α β) (i : α) : β :=
a i

lemma arrayext (a₁ a₂ : array α β) : (∀ i, select a₁ i = select a₂ i) → a₁ = a₂ :=
funext

variable [decidable_eq α]

def store (a : array α β) (i : α) (v : β) : array α β :=
λ j, if j = i then v else select a j

@[simp] lemma select_store (a : array α β) (i : α) (v : β) : select (store a i v) i = v :=
by unfold smt.store smt.select; rewrite if_pos; reflexivity

@[simp] lemma select_store_ne (a : array α β) (i j : α) (v : β) : j ≠ i → select (store a i v) j = select a j :=
by intros; unfold smt.store smt.select; rewrite if_neg; assumption

end smt
