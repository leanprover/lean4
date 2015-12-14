import data.nat
open nat

constants f : nat → nat → nat
axiom f_ax  : ∀ a b, f a b = f b a

example (a b : nat) : f a b = f b a :=
begin
  with_attrs f_ax [simp] simp
end

definition g (a : nat) := f a 1

example (a : nat) : g a = f 1 a :=
begin
  with_attributes g [reducible] with_attributes f_ax [simp] simp
end
