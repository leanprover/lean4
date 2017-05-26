open tactic
theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → nat))
:= by apply_instance

#print H
