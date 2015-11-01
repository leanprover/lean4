section
variables a b c : nat
variable  H1 : a = b
variable  H2 : a + b + a + b = 0

example : b + b + a + b = 0 :=
  @@eq.rec_on (λ x, x + b + a + b = 0) H1 H2
end

section
variables (f : Π {T : Type₁} {a : T} {P : T → Prop}, P a → Π {b : T} {Q : T → Prop}, Q b → Prop)
variables (T : Type₁) (a : T) (P : T → Prop) (pa : P a)
variables (b : T) (Q : T → Prop) (qb : Q b)

check @f T a P pa b Q qb -- Prop
check @@f P pa Q qb      -- Prop
check f pa qb            -- Prop
end
