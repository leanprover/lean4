run_cmd mk_simp_attr `boo
run_cmd mk_simp_attr `bla

constant f : nat → nat

set_option trace.user_attributes_cache true

@[boo] lemma ex : ∀ x, f x = 1 :=
sorry

example : f 0 = 1 :=
by simp with boo

#print "----"

example : f 2 = 1 :=
by simp with boo

#print "----"

constant g : nat → nat

@[boo] lemma ex2 : ∀ x, g x = x :=
sorry

constant h : nat → nat

@[bla] lemma ex3 : ∀ x, h x = x :=
sorry

example : f 2 = g 1 :=
by simp with boo

#print "-------"

example : f 2 = h (g 1) :=
by simp with boo bla
