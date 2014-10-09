import logic
open eq.ops
set_option pp.notation false
section
  variable  {A : Type}
  variables {a b c d e : A}
  theorem tst : a = b → b = c → c = d → d = e → a = e :=
  take H1 H2 H3 H4,
  have e1 : a = c,
  proof
    @eq.trans _ _ _ _ H1 H2
  ∎,
  e1 ⬝ H3 ⬝ H4
end
