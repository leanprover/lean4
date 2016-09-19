set_option new_elaborator true
open tactic

section
  variable {A : Type}
  variable {B : Type}
  variable Ha : inhabited A
  variable Hb : inhabited B
  include Ha Hb
  theorem tst : inhabited (Prop × A × B) := by apply_instance

end

reveal tst
print tst
