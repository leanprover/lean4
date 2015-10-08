import algebra.ring -- has_add, has_one, ... will be moved to init in the future
open algebra

variable {A : Type}

definition zero [s : has_zero A] : A :=
has_zero.zero A

definition one [s : has_one A] : A :=
has_one.one A

definition add [s : has_add A] : A → A → A :=
has_add.add

definition bit0 [s : has_add A] (a : A) : A :=
add a a

definition bit1 [s₁ : has_add A] [s₂ : has_one A] (a : A) : A :=
add (add a a) one

-- variables [s : ring A]
-- set_option pp.all true
-- check bit1 (bit0 (one : A))
