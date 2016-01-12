open nat subtype

definition f (x : nat) (y : {n : nat | n > x}) : nat :=
x + elt_of y

set_option blast.subst false

example (h : nat → nat) (a b c d : nat) (Ha : h c > h a) (Hb : h d > h b)
        : h a = h b → c = d → f (h a) (tag (h c) Ha) = f (h b) (tag (h d) Hb) :=
by inst_simp
