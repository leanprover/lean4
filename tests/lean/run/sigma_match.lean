open sigma

constant hom.{l₁ l₂} {A : Type.{l₁}} {B : Type.{l₂}} (a : A) (b : B) : Type.{max l₁ l₂}

definition arrow_ob [reducible] (A B : Type) : Type :=
Σ (a : A) (b : B), hom a b

definition src1 {A B : Type} (x : arrow_ob A B) : A :=
match x with
  ⟨a, b, h⟩ := a
end

definition src2 {A B : Type} : arrow_ob A B → A
| src2 ⟨a, _, _⟩ := a

definition src3 {A B : Type} (x : arrow_ob A B) : A :=
match x with
  ⟨a, _, _⟩ := a
end

example (A B : Type) (x : arrow_ob A B) : src1 x = src2 x :=
rfl

example (A B : Type) (x : arrow_ob A B) : src1 x = src3 x :=
rfl

example (A B : Type) (x : arrow_ob A B) : src2 x = src3 x :=
rfl
