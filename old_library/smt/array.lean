/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
namespace smt
definition array (A B : Type) := A → B

variables {A B : Type}
open tactic

definition select (a : array A B) (i : A) : B :=
a i

theorem arrayext (a₁ a₂ : array A B) : (∀ i, select a₁ i = select a₂ i) → a₁ = a₂ :=
funext

variable [decidable_eq A]

definition store (a : array A B) (i : A) (v : B) : array A B :=
λ j, if j = i then v else select a j

theorem select_store [simp] (a : array A B) (i : A) (v : B) : select (store a i v) i = v :=
by unfold [`smt.store, `smt.select] >> dsimp >> rewrite `if_pos >> reflexivity

theorem select_store_ne [simp] (a : array A B) (i j : A) (v : B) : j ≠ i → select (store a i v) j = select a j :=
by intros >> unfold [`smt.store, `smt.select] >> dsimp >> rewrite `if_neg >> assumption

end smt
