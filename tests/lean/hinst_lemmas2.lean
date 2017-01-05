run_command mk_hinst_lemma_attr_set `attr_main [`attr1, `attr2] [`sattr1, `sattr2]

constant f : nat → nat
constant g : nat → nat → nat
constant p : nat → Prop

constant fax1 : ∀ x, f x = g x x
constant gax1 : ∀ x y, p x → p y → g x y = x
constant gax2 : ∀ x y, g x y = 0 → g x (f y) = g x y
constant gax3 : ∀ x, g x x = f x
constant gax4 : ∀ x y, (: g x (f y) :) = 0 → g y x = 1
constant gax5 : ∀ x y z, p y → g x z = 0 → g y x = 1
constant gax6 : ∀ x y, g x y = g y x

attribute [attr_main] fax1
attribute [attr1] gax1
attribute [sattr2] gax2
attribute [attr2] gax3
attribute [attr2] gax4
attribute [attr_main] gax5
attribute [sattr1] gax6

run_command get_hinst_lemmas_for_attr `attr_main >>= hinst_lemmas.pp >>= tactic.trace
