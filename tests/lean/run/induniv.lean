inductive list (A : Type) : Type :=
| nil {} : list A
| cons   : A → list A → list A

section
  parameter A : Type
  inductive list2 : Type :=
  | nil2 {} : list2
  | cons2   : A → list2 → list2
end

variable num : Type.{1}

namespace Tree
inductive tree (A : Type) : Type :=
| node : A → forest A → tree A
with forest (A : Type) : Type :=
| nil  : forest A
| cons : tree A → forest A → forest A
end Tree

inductive group_struct (A : Type) : Type :=
| mk_group_struct : (A → A → A) → A → group_struct A

inductive group : Type :=
| mk_group : Π (A : Type), (A → A → A) → A → group

section
  parameter A : Type
  parameter B : Type
  inductive pair : Type :=
  | mk_pair : A → B → pair
end

definition Prop [inline] := Type.{0}
inductive eq {A : Type} (a : A) : A → Prop :=
| refl : eq a a

section
  parameter {A : Type}
  inductive eq2 (a : A) : A → Prop :=
  | refl2 : eq2 a a
end


section
  parameter A : Type
  parameter B : Type
  inductive triple (C : Type) : Type :=
  | mk_triple : A → B → C → triple C
end
