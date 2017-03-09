inductive imf (f : nat → nat) : nat → Type
| mk1 : ∀ (a : nat), imf (f a)
| mk2 : imf (f 0 + 1)

definition inv_2 (f : nat → nat) : ∀ (b : nat), imf f b → {x : nat // x > b} → nat
| .(f a)     (imf.mk1 .f a) x := a
| .(f 0 + 1) (imf.mk2 .f)   x := subtype.val x
