/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.wf init.nat
namespace nat

private definition div_rec_lemma {x y : nat} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, and.rec (λ ypos ylex, sub_lt (nat.lt_of_lt_of_le ypos ylex) ypos) h

private definition div.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y + 1 else zero

protected definition div := well_founded.fix lt_wf div.F

instance : has_div nat :=
⟨nat.div⟩

theorem div_def (x y : nat) : div x y = if H : 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 :=
congr_fun (well_founded.fix_eq lt_wf div.F x) y

private definition mod.F (x : nat) (f : Π x₁, x₁ < x → nat → nat) (y : nat) : nat :=
if H : 0 < y ∧ y ≤ x then f (x - y) (div_rec_lemma H) y else x

protected definition mod := well_founded.fix lt_wf mod.F

instance : has_mod nat :=
⟨nat.mod⟩

theorem mod_def (x y : nat) : mod x y = if H : 0 < y ∧ y ≤ x then mod (x - y) y else x :=
congr_fun (well_founded.fix_eq lt_wf mod.F x) y

end nat
