open sigma

constant {l₁ l₂} hom {A : Type l₁} {B : Type l₂} (a : A) (b : B) : Type (max l₁ l₂)

attribute [reducible]
noncomputable definition arrow_ob (A B : Type) : Type :=
Σ (a : A) (b : B), hom a b

noncomputable definition src1 {A B : Type} (x : arrow_ob A B) : A :=
match x with
  (sigma.mk a (sigma.mk b h)) := a
end

noncomputable definition src2 {A B : Type} : arrow_ob A B → A
| (sigma.mk a (sigma.mk b c)) := a

noncomputable definition src3 {A B : Type} (x : arrow_ob A B) : A :=
match x with
  (sigma.mk a (sigma.mk b c)) := a
end

example (A B : Type) (x : arrow_ob A B) : src1 x = src2 x :=
rfl

example (A B : Type) (x : arrow_ob A B) : src1 x = src3 x :=
rfl

example (A B : Type) (x : arrow_ob A B) : src2 x = src3 x :=
rfl
