open prod inhabited

definition H : inhabited (Prop × nat × (nat → nat)) :=
by tactic.apply_instance

#print H
