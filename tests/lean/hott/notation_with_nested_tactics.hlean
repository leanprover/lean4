open is_equiv
constants (A B : Type) (f : A → B)

definition H : is_equiv f := sorry


definition loop [instance] [h : is_equiv f] : is_equiv f :=
h

notation `noinstances` t:max := by+ with_options [elaborator.ignore_instances true] (exact t)

example (a : A) : let H' : is_equiv f := H in @(inv f) H' (f a) = a :=
noinstances (left_inv f a)
