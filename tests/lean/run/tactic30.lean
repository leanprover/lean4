import standard
using tactic

section
  set_option pp.universes true
  set_option pp.implicit  true
  parameter  {A : Type}
  parameters {a b : A}
  parameter  H : a = b
  theorem test : a = b ∧ a = a
  := including H, by apply and_intro; assumption; apply refl
end

check @test