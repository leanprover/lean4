constant p : nat → Prop
constant q : ∀ a, p a → Prop
lemma ex [forward] : ∀ (a : nat) (h : p a), (:q a h:) := sorry

set_option blast.strategy "ematch"

lemma test (h : p 0) : q 0 h :=
by blast
