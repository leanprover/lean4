import logic
set_option pp.universes true

universe u
variable A : Type.{u}

definition id1 (a : A) : A := a
check @id1

variable B : Type

definition id2 (a : B) : B := a
check @id2

universe variable k
variable C : Type.{k}

definition id3 (a : C) := a

check @id3

universe variables l m
variable A₁ : Type.{l}
variable A₂ : Type.{l}
definition foo (a₁ : A₁) (a₂ : A₂) := a₁ == a₂
check @foo

check Type.{m}
