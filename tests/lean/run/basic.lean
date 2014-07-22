variable A.{l1 l2} : Type.{l1} → Type.{l2}
check A
definition tst.{l} (A : Type) (B : Type) (C : Type.{l}) : Type := A → B → C
check tst
variable group.{l} : Type.{l+1}
variable carrier.{l} : group.{l} → Type.{l}
definition to_carrier (g : group) := carrier g

check to_carrier.{1}

section
  parameter A : Type
  check A
  definition B := A → A
end
variable N : Type.{1}
check B N
variable f : B N
check f
variable a : N
check f a

section
  parameter T1 : Type
  parameter T2 : Type
  parameter f : T1 → T2 → T2
  definition double (a : T1) (b : T2) := f a (f a b)
end

check double
check double.{1 2}

definition Prop [inline] := Type.{0}
variable eq : Π {A : Type}, A → A → Prop
infix `=`:50 := eq

check eq.{1}

section
  universe l
  universe u
  parameter {T1 : Type.{l}}
  parameter {T2 : Type.{l}}
  parameter {T3 : Type.{u}}
  parameter f  : T1 → T2 → T2
  definition is_proj2 := ∀ x y, f x y = y
  definition is_proj3 (f : T1 → T2 → T3 → T3) := ∀ x y z, f x y z = z
end

check @is_proj2.{1}
check @is_proj3.{1 2}

namespace foo
section
  parameters {T1 T2 : Type}
  parameter  {T3 : Type}
  parameter  f : T1 → T2 → T2
  definition is_proj2 := ∀ x y, f x y = y
  definition is_proj3 (f : T1 → T2 → T3 → T3) := ∀ x y z, f x y z = z
end
check @foo.is_proj2.{1}
check @foo.is_proj3.{1 2}
end

namespace bla
section
  parameter  {T1 : Type}
  parameter  {T2 : Type}
  parameter  {T3 : Type}
  parameter  f : T1 → T2 → T2
  definition is_proj2 := ∀ x y, f x y = y
  definition is_proj3 (f : T1 → T2 → T3 → T3) := ∀ x y z, f x y z = z
end
check @bla.is_proj2.{1 2}
check @bla.is_proj3.{1 2 3}
end