open nat subtype

definition f (x : nat) (y : {n : nat | n > x}) : nat :=
x + elt_of y

definition f_flat (x : nat) (y : nat) (H : y > x) : nat :=
f x (tag y H)

lemma f_flat_simp [forward] (x : nat) (y : nat) (H : y > x) : f x (tag y H) = f_flat x y H :=
rfl

set_option trace.simplifier true
set_option trace.blast true
set_option blast.strategy "ematch"

example (a b c d : nat) (Ha : c > a) (Hb : d > b) : a = b → c = d → f a (tag c Ha) = f b (tag d Hb) :=
by blast

example (h : nat → nat) (a b c d : nat) (Ha : h c > h a) (Hb : h d > h b)
        : h a = h b → c = d → f (h a) (tag (h c) Ha) = f (h b) (tag (h d) Hb) :=
by blast
