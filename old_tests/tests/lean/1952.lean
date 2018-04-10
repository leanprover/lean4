structure foo :=
(fn    : nat → nat)
(fn_ax : ∀ a : nat, fn a = a)

/-
set_option pp.all true
set_option pp.universes false                 -- universes are probably irrelevant
set_option pp.purify_metavars false
set_option trace.type_context.is_def_eq true
set_option trace.type_context.is_def_eq_detail true
-/

def bla : foo := { fn_ax := λ x, rfl }


instance foo2 (α : Type) : group α := { mul_assoc := λ x y z, rfl }
