open is_equiv
constants (A B : Type) (f : A → B)

definition H : is_equiv f := sorry


definition loop [instance] [h : is_equiv f] : is_equiv f :=
h

example (a : A) : let H' : is_equiv f := H in @(is_equiv.inv f) H' (f a) = a :=
begin
  with_options [elaborator.ignore_instances true] (apply left_inv f a)
end
