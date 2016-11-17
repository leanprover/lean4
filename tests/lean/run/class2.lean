open tactic
theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → num))
:= by apply_instance

print H
