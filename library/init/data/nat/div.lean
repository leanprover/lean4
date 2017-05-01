/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.wf init.data.nat.basic
namespace nat

private def div_rec_lemma {x y : nat} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, and.rec (λ ypos ylex, sub_lt (nat.lt_of_lt_of_le ypos ylex) ypos) h

private def div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y + 1 else zero

protected def div := well_founded.fix lt_wf div.F

instance : has_div nat :=
⟨nat.div⟩

lemma div_def_aux (x y : nat) : x / y = if h : 0 < y ∧ y ≤ x then (x - y) / y + 1 else 0 :=
congr_fun (well_founded.fix_eq lt_wf div.F x) y

private def mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if h : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma h) y else x

protected def mod := well_founded.fix lt_wf mod.F

instance : has_mod nat :=
⟨nat.mod⟩

lemma mod_def_aux (x y : nat) : x % y = if h : 0 < y ∧ y ≤ x then (x - y) % y else x :=
congr_fun (well_founded.fix_eq lt_wf mod.F x) y

end nat
