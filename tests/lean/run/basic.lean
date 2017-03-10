prelude

constant {l1 l2} A : Type l1 → Type l2
#check A
definition {l} tst (A : Type*) (B : Type*) (C : Type l) : Type* := A → B → C
#check tst
constant {l} group : Type (l+1)
constant {l} carrier : group.{l} → Type l
noncomputable definition to_carrier (g : group) := carrier g

#check to_carrier.{1}

section
  variable A : Type*
  #check A
  definition B := A → A
end
constant N : Type 1
#check B N
constant f : B N
#check f
constant a : N
#check f a

section
  variable T1 : Type*
  variable T2 : Type*
  variable f : T1 → T2 → T2
  definition double (a : T1) (b : T2) := f a (f a b)
end

#check double
#check double.{1 2}

definition Prop := Type 0
constant Eq : Π {A : Type*}, A → A → Prop
infix `=`:50 := Eq

#check Eq.{1}

section
  universe variable l
  universe variable u
  variable {T1 : Type l}
  variable {T2 : Type l}
  variable {T3 : Type u}
  variable f  : T1 → T2 → T2
  noncomputable definition is_proj2 := ∀ x y, f x y = y
  noncomputable definition is_proj3 (f : T1 → T2 → T3 → T3) := ∀ x y z, f x y z = z
end

#check @is_proj2.{1}
#check @is_proj3.{1 2}

namespace foo
section
  universe variables u v
  variables {T1 T2 : Type u}
  variable  {T3 : Type v}
  variable  f : T1 → T2 → T2
  noncomputable definition is_proj2 := ∀ x y, f x y = y
  noncomputable definition is_proj3 (f : T1 → T2 → T3 → T3) := ∀ x y z, f x y z = z
end
#check @foo.is_proj2.{1}
#check @foo.is_proj3.{1 2}
end foo

namespace bla
section
  variable  {T1 : Type*}
  variable  {T2 : Type*}
  variable  {T3 : Type*}
  variable  f : T1 → T2 → T2
  noncomputable definition is_proj2 := ∀ x y, f x y = y
  noncomputable definition is_proj3 (f : T1 → T2 → T3 → T3) := ∀ x y z, f x y z = z
end
#check @bla.is_proj2.{1 2}
#check @bla.is_proj3.{1 2 3}
end bla
