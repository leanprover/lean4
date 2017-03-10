open tactic

section
  variable {A : Type}
  variable {B : Type}
  variable Ha : inhabited A
  variable Hb : inhabited B
  include Ha Hb
  theorem tst : inhabited (Prop × A × B) := by apply_instance

end

#print tst
