set_option new_elaborator true
open tactic
theorem H {A B : Type} (H1 : inhabited A) : inhabited (Prop × A × (B → num))
:= by apply_instance

reveal H
print H
