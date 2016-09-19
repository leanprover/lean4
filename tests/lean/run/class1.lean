set_option new_elaborator true
open prod inhabited

definition H : inhabited (Prop × num × (num → num)) :=
by tactic.apply_instance

print H
