open subtype nat

constant f : Π (a : nat), {b : nat | b > a} → nat

definition f_flat (a : nat) (b : nat) (p : b > a) : nat :=
f a (tag b p)

definition greater [reducible] (a : nat) := {b : nat | b > a}
set_option blast.recursion.structure true

definition f_flat_def [simp] (a : nat) (b : nat) (p : b > a) : f a (tag b p) = f_flat a b p :=
rfl

definition has_property_tag [simp] {A : Type} {p : A → Prop} (a : A) (h : p a) : has_property (tag a h) = h :=
rfl

lemma to_f_flat : ∀ (a : nat) (b : greater a), f a b = f_flat a (elt_of b) (has_property b) :=
by rec_simp
