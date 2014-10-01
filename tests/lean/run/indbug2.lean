set_option pp.implicit true
set_option pp.universes true
section
parameter {A : Type}
definition foo : A → A → Type := (λ x y, Type)
inductive bar {a b : A} (f : foo a b) :=
bar2 : bar f
end
