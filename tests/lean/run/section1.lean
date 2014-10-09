import logic
open tactic

section
  set_option pp.universes true
  set_option pp.implicit  true
  variable  {A : Type}
  variables {a b : A}
  variable  H : a = b
  variables H1 H2 : b = a
  check H1
  check H
  check H2
end
