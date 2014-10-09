import logic
open tactic

section
  set_option pp.universes true
  set_option pp.implicit  true
  variable  {A : Type}
  variables {a b : A}
  variable  H : a = b
  include H
  theorem test : a = b ∧ a = a
  := by apply and.intro; assumption; apply eq.refl
end

check @test
